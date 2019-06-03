use reo_rs::rbpa::StatePred;

use hashbrown::HashMap;
use reo_rs::proto::traits::Proto;

use reo_rs::set;
use reo_rs::LocId;

// use std::io::Write;
use itertools::Itertools;
use num_bigint::BigUint;
use std::fmt;

fn main() {
    let port_set = set! {0,1};

    // let mut s = String::new();

    // 1. fetch the RBPA, projected onto your port set
    let mut rbpa = reo_rs_proto::Fifo3::<()>::proto_def()
        .new_rbpa(&port_set)
        .expect("WAH");
    println!("RBPA START: {:#?}", &rbpa);

    // 2. normalize RBPA (removing silent transitions)
    rbpa.normalize();

    // 3. compute which pairs of rules are mutually exclusive
    let mutex_pairs = (0..rbpa.rules.len())
        .combinations(2)
        .filter_map(|c| {
            if c[0] < c[1] && rbpa.rules[c[0]].is_mutex_with(&rbpa.rules[c[1]]) {
                Some([c[0], c[1]])
            } else {
                None
            }
        });
    // println!("mutex_pairs {:?}", &mutex_pairs);

    // 4. 
    let p = powerset(rbpa.rules.len(), mutex_pairs);
    if p.len() > 200 {
        panic!("POWERSET TOO HUGE");
    }
    let mut clusters: Vec<(Vec<LocId>, StatePred)> = p
        .into_iter()
        .map(|set| {
            let mut guard = HashMap::default();
            for &s in set.iter() {
                rbpa.rules[s].constrain_guard(&mut guard).expect("oops");
            }
            (set, guard)
        })
        .collect();
    println!("clusters:");
    for (i, (set, guard)) in clusters.iter().enumerate() {
        println!("c{}\t {:?}: {:?}", i, PrintableGuard(guard), set);
    }
    let mut to_drop = vec![];
    for g in clusters.iter().enumerate().combinations(2) {
        let (ai, (ak, av)) = g[0];
        let (bi, (bk, bv)) = g[1];
        if av == bv {
            if ak.len() > bk.len() {
            	if superset_vec(ak, bk) {
                	to_drop.push(bi);
	                println!("{:?} encompasses {:?} for guard {:?}", ak, bk, av);
	            }
            } else if ak.len() < bk.len() {
            	if superset_vec(bk, ak) {
	                to_drop.push(ai);
	                println!("{:?} encompasses {:?} for guard {:?}", bk, ak, av);
            	}
            }
        }
    }
    to_drop.sort();
    to_drop.dedup();
    for &d in to_drop.iter().rev() {
        clusters.remove(d);
    }
    println!("============");
    let rule_set: Vec<_> = clusters
        .iter()
        .flat_map(|x| x.0.iter())
        .copied()
        .unique()
        .collect();
    // let mutex_set: HashSet<[LocId;2]> = mutex_pairs.iter().copied().collect();
    let done = clusters.into_iter().filter_map(|(rules, guard)| {
        println!("{:?}:\tguard: {:?}", rules, PrintableGuard(&guard));
        let mut excluded: Vec<(StatePred, Vec<usize>)> = vec![];
        'outer: for &excluded_rid in &rule_set {
            if rules.contains(&excluded_rid) {
                continue; // rule is INCLUDED!
            }
            // must exclude!
            let excluded_guard = rbpa.rules[excluded_rid].get_guard();
            if guard_conflict(excluded_guard, &guard) {
            	// implicitly excluded by guard already
            	continue 'outer;
            }
            for (e_guard, e_rules) in excluded.iter_mut() {
                if let Some(exc_fused) = fuse_guards(e_guard, excluded_guard) {
                    if implies(&guard, &exc_fused) {
            			// the guard is unsatisfiable
            			println!("shadowed by (fused) {:?}", PrintableGuard(&exc_fused));
                        return None;
                    }
                    e_rules.push(excluded_rid);
                    *e_guard = exc_fused;
                    continue 'outer;
                }
            }
            if implies(&guard, excluded_guard) {
            			// the guard is unsatisfiable
    			println!("unsatisfiable {:?}", PrintableGuard(excluded_guard));
                return None;
            }
            excluded.push((excluded_guard.clone(), vec![excluded_rid]));
        }
        for (e_guard, e_rules) in excluded.iter() {
            println!(" - exclude: {:?}", (PrintableGuard(e_guard), e_rules));
        }
        println!("RETAIN..");
        excluded.retain(|x| !guard_conflict(&guard, &x.0));
        for (e_guard, e_rules) in excluded.iter() {
            println!(" - exclude: {:?}", (PrintableGuard(e_guard), e_rules));
        }
        Some((rules, guard, excluded))
    }).collect::<Vec<_>>();
    println!(" =================\n FINISHED");
    let empty_assign = HashMap::default();
    for (rules, guard, excluded) in done.iter() {
    	let assign = if let Some(rule_id) = rules.iter().copied().next() {
        	rbpa.rules[rule_id].get_assign()
        } else {
        	&empty_assign
        };
        println!(
            "rules: {:?}\tguard: {:?}\tassign: {:?}\texcluded: {:?}",
            rules,
            PrintableGuard(&guard),
            PrintableGuard(assign),
            excluded
                .iter()
                .map(|x| PrintableGuard(&x.0))
                .collect::<Vec<_>>()
        );
    }

    let mut matches = vec![];
    for state in (SanityCheck { x:0 }) {
    	matches.clear();
    	matches.extend(done.iter().enumerate().filter_map(
    		|(i, (_rules, guard, excluded))| {
    		if guard_conflict(guard, &state) {
    			return None
    		} else {
    			for ex in excluded.iter() {
    				if !guard_conflict(&ex.0, &state) {
		    			return None
		    		}
    			}
    		}
    		Some(i)
    	}));
    	if matches.len() != 1 {
    		println!("- {:?} has matches {:?}", PrintableGuard(&state), &matches);
    	} else {
    		println!("+ {:?} PERFECT {:?}", PrintableGuard(&state), &matches);
    	}
    }
}

fn superset_vec(a: &Vec<LocId>, b: &Vec<LocId>) -> bool {
	for x in b.iter() {
		if !a.contains(x) {
			return false
		}
	}
	true
}

struct SanityCheck {
	x: usize,
}
impl<'a> SanityCheck {
    const NUM_CELLS: usize = 3;
}
impl<'a> Iterator for SanityCheck {
	type Item = StatePred;
	fn next(&mut self) -> Option<Self::Item> {
		const STOP: usize = !0;
		if self.x == STOP {
			None
		} else {
			let mut x = HashMap::default();
			for i in 0..Self::NUM_CELLS {
				let val = if ((self.x >> i) % 2) == 1 {
					true
				} else {
					false
				};
				x.insert(i + 2, val);
			}
			self.x += 1;
			if self.x == (1 << Self::NUM_CELLS) {
				self.x = STOP;
			}
			Some(x)
		}
	}
}

struct PrintableGuard<'a>(&'a StatePred);
impl<'a> fmt::Debug for PrintableGuard<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut buf = vec!['.'; 5];
        for (&k, &v) in self.0.iter() {
            if buf.len() <= k {
                buf.resize_with(k + 1, || '.');
            }
            buf[k] = if v { 'T' } else { 'F' };
        }
        for b in buf.drain(..) {
            write!(f, "{}", b)?;
        }
        Ok(())
    }
}

enum FuseCase {
    LeftSubsumes,
    RightSubsumes,
    PartitionAt(LocId),
    Identical,
}

fn guard_conflict(a: &StatePred, b: &StatePred) -> bool {
	for (id, x) in a.iter() {
        match b.get(id) {
            Some(y) if x != y => return true,
            _ => (),
        }
    }
    false
}

/// returns true if 
fn implies(anticedent: &StatePred, consequent: &StatePred) -> bool {
	if guard_conflict(anticedent, consequent) {
		return false
	}
	for id in consequent.keys() {
		if !anticedent.contains_key(id) {
			return false
		}
	}
    true
}

fn fuse_guards(l: &StatePred, r: &StatePred) -> Option<StatePred> {
    use FuseCase::*;
    let mut g_case = Identical;
    for id in l.keys().chain(r.keys()).unique() {
        match [l.get(id), r.get(id)] {
            [Some(_), None] => match g_case {
                RightSubsumes | Identical => g_case = RightSubsumes,
                _ => return None,
            },
            [None, Some(_)] => match g_case {
                LeftSubsumes | Identical => g_case = LeftSubsumes,
                _ => return None,
            },
            [Some(a), Some(b)] if a != b => match g_case {
                Identical => g_case = PartitionAt(*id),
                _ => return None,
            },
            [Some(_), Some(_)] => (),
            [None, None] => unreachable!(),
        }
    }
    Some(match g_case {
        Identical | LeftSubsumes => l.clone(),
        RightSubsumes => r.clone(),
        PartitionAt(id) => {
            let mut x = l.clone();
            let _ = x.remove(&id);
            x
        }
    })
}

/// Given an end to a range of port ids (presuming port range 0..`rng_end`)
/// (exclusive!) and a list of ids whose guards render them mutually-exclusively
/// applicable to states (eg: TTT and FXX).
///
/// It produces the powerset construction of these port IDs, omitting any sets
/// that contain both elements of any mutex pair.
fn powerset<I>(rng_end: LocId, mutex_pairs: I) -> Vec<Vec<LocId>>
where
    I: IntoIterator<Item = [LocId; 2]>,
{
    // 1. initialize and defines an auxiliary closure for computing whether
    // the current counter represents a set containing the given id.
    let zero = BigUint::default();
    let mut temp = BigUint::new(vec![1]);
    let mut counter_contains = move |counter: &BigUint, id: LocId| {
        temp.assign_from_slice(&[1]);
        temp <<= id;
        temp &= counter;
        // temp is now either 2^id or 0. 0 means "counter DOES contain this element"
        temp == zero
    };

    let mut one = BigUint::new(vec![1]);
    let mut mutex_mask: Vec<_> = std::iter::repeat_with(|| BigUint::default())
        .take(rng_end)
        .collect();

    // 2. precompute the "jump distances" in the counter for every port.
    // mutex_mask now stores 0 for every id in 0..`rng_end`
    for [mut a, mut b] in mutex_pairs.into_iter() {
        if a < b {
            std::mem::swap(&mut a, &mut b);
        }
        if a > b {
            one <<= b;
            mutex_mask[a] |= &one;
            one >>= b;
        }
    }
    // mutex_mask[a] stores a bit 1 for every index `b` where:
    // * a > b
    // * ports a and b are mutex

    // 3. Iterate over the set-space and jump over those that represent
    // sets containing 1+ mutual exclusion groups. 
    let mut sets = vec![];
    let mut counter = BigUint::default();
    let counter_cap = {
        let mut x = BigUint::new(vec![1]);
        x <<= rng_end;
        x
    };
    while counter < counter_cap {
        // In this instant, `counter` represents a port set in its bits
        // 0s correspond to PRESENCE. 1s correspond to ABSENCE.
        // eg for port range 0..4: 0b01000 is the set {0,1,2,4}
        // (also: safe to skip 0th mask. it's always empty)
        for a in (1..rng_end).rev() {
            if counter_contains(&counter, a) {
                // SET all bits mutex with a at once.
                // corresponds with removing these bits from the set
                // results in chunks of the iteration space being skipped
                // which would have contained mutex pairs
                counter |= &mutex_mask[a];
            }
        }
        let set = (0..rng_end)
            .clone()
            .filter(|&x| counter_contains(&counter, x))
            .collect();
        sets.push(set);
        counter += &one;
    }
    sets
}

/*
TODO encompass step must be sped up somehow
TODO investigate further minimizing RBPAs. Note some shit explodes.
-- idea: what is consequence of adding ..... -1-> ..... rules?
*/

// struct PowerSetIter {
//     // guard_buf: &'a mut StatePred,
//     // locs_buf: &'a mut Vec<LocId>,
//     mutex_masks: Vec<BigUint>,
//     counter: BigUint,
//     one: BigUint,
//     counter_cap: BigUint,
//     zero: BigUint,
//     temp: BigUint,
// }
// impl Iterator for PowerSetIter {
//     type Item = Vec<LocId>;
//     fn next(&mut self) -> Option<Self::Item> {

//         fn counter_contains(me: &mut PowerSetIter, id: LocId) -> bool {
//             me.temp.assign_from_slice(&[1]);
//             me.temp <<= id;
//             me.temp &= me.counter;
//             me.temp == me.zero
//         }

//         if self.counter < self.counter_cap {
//             // In this instant, `counter` represents a port set in its bits
//             // 0s correspond to PRESENCE. 1s correspond to ABSENCE.
//             // eg for port range 0..4: 0b01000 is the set {0,1,2,4}
//             // (also: safe to skip 0th mask. it's always empty)
//             for (i, m) in self.mutex_masks.iter().skip(1).enumerate().rev() {
//                 if counter_contains(self, i) {
//                     // SET all bits mutex with a at once.
//                     // corresponds with removing these bits from the set
//                     // results in chunks of the iteration space being skipped
//                     // which would have contained mutex pairs
//                     self.counter |= m;
//                 }
//             }
//             let mut locs_buf = vec![];
//             // self.locs_buf.clear();
//             for i in (0..self.mutex_masks.len()).filter(|&x| counter_contains(self, x)) {
//                 locs_buf.push(i);
//             }
//             self.counter += &self.one;
//             Some(locs_buf)
//         } else {
//             None
//         }
//     }
// }
// impl PowerSetIter {
//     fn new<M>(rng_end: LocId, mutex_pairs: M) -> Self
//     where M: IntoIterator<Item = [LocId; 2]> {
//         let mut one = BigUint::new(vec![1]);
//         let mut mutex_masks: Vec<_> = std::iter::repeat_with(|| BigUint::default())
//             .take(rng_end).collect();
//         for [mut a, mut b] in mutex_pairs {
//             if a < b {
//                 std::mem::swap(&mut a, &mut b);
//             }
//             if a > b {
//                 one <<= b;
//                 mutex_masks[a] |= &one;
//                 one >>= b;
//             }
//         }
//         Self {
//             // guard_buf,
//             // locs_buf,
//             counter: BigUint::default(),
//             one,
//             counter_cap: {
//                 let mut x = BigUint::new(vec![1]);
//                 x <<= rng_end;
//                 x
//             },
//             mutex_masks,
//             zero: BigUint::default(),
//             temp: BigUint::default(),
//         }
//     }
// }