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
    let port_set = set! {0, 1};
    let _out = String::new();
    let mut rbpa = reo_rs_proto::Fifo3::<()>::proto_def()
        .new_rbpa(&port_set)
        .expect("WAH");
    rbpa.normalize();
    let mutex_pairs: Vec<[LocId; 2]> = (0..rbpa.rules.len())
        .combinations(2)
        .filter_map(|c| {
            if c[0] < c[1] && rbpa.rules[c[0]].is_mutex_with(&rbpa.rules[c[1]]) {
                Some([c[0], c[1]])
            } else {
                None
            }
        })
        .collect();
    println!("mutex_pairs {:?}", &mutex_pairs);
    let p = powerset(rbpa.rules.len(), mutex_pairs.iter().copied());
    let mut clusters: Vec<_> = p
        .into_iter()
        .map(|set| {
            let mut guard = HashMap::default();
            for &s in set.iter() {
                rbpa.rules[s].constrain_guard(&mut guard).expect("oops");
            }
            (set, guard)
        })
        .collect();
    for g in clusters.iter() {
        println!("{:?}", g);
    }
    let mut to_drop = vec![];
    for g in clusters.iter().enumerate().combinations(2) {
        let (ai, (ak, av)) = g[0];
        let (bi, (bk, bv)) = g[1];
        if av == bv {
            if ak.len() > bk.len() {
                to_drop.push(bi);
                println!("{:?} encompasses {:?} for guard {:?}", ak, bk, av);
            } else {
                to_drop.push(ai);
                println!("{:?} encompasses {:?} for guard {:?}", bk, ak, av);
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
        'outer: for &rule_id in &rule_set {
            if rules.contains(&rule_id) {
                continue; // rule is INCLUDED!
            }
            // println!("is {:?}", excluded.iter().map(|x| PrintableGuard(x)).collect::<Vec<_>>());

            // must exclude!
            let rule_guard = rbpa.rules[rule_id].get_guard();
            for (e_guard, e_rules) in excluded.iter_mut() {
                if let Some(fused) = fuse_guards(e_guard, rule_guard) {
                    if guard_shadowed(&guard, &fused) {
                        println!("SHADOWED");
                        return None;
                    }
                    *e_guard = fused;
                    e_rules.push(rule_id);
                    // println!("fuse succeeded");
                    continue 'outer;
                }
            }
            // failed to fuse. add it.
            if guard_shadowed(&guard, rule_guard) {
                println!("SHADOWED");
                return None;
            }
            excluded.push((rule_guard.clone(), vec![rule_id]));
        }
        for (e_guard, e_rules) in excluded.iter() {
            println!(" - exclude: {:?}", (PrintableGuard(e_guard), e_rules));
        }
        Some((rules, guard, excluded))
    }).collect::<Vec<_>>();
    println!(" =================\n FINISHED");
    for (rules, guard, excluded) in done {
        println!(
            "{:?}:\tguard: {:?}\texcluded: {:?}",
            rules,
            PrintableGuard(&guard),
            excluded
                .iter()
                .map(|x| PrintableGuard(&x.0))
                .collect::<Vec<_>>()
        );
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

fn guard_shadowed(shadowed: &StatePred, shadowing: &StatePred) -> bool {
    for (id, x) in shadowed.iter() {
        match shadowing.get(id) {
            Some(y) if x != y => return false,
            _ => (),
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
    // initializes and defines an auxiliary closure for computing whether
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
    // 1. a > b
    // 2. ports a and b are mutex

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
        for a in (0..rng_end).rev() {
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
