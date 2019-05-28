use hashbrown::HashMap;
use reo_rs::proto::traits::Proto;

use reo_rs::set;
use reo_rs::LocId;
use std::ops::Range;
// use std::io::Write;
use itertools::Itertools;

fn main() {
    let port_set = set! {0, 1};
    let _out = String::new();
    let mut rbpa = reo_rs_proto::Fifo3::<()>::proto_def()
        .new_rbpa(&port_set)
        .expect("WAH");
    rbpa.normalize();
    let mutex_pairs: Vec<(LocId, LocId)> = (0..rbpa.rules.len())
        .combinations(2)
        .filter_map(|c| {
            if c[0] < c[1] && rbpa.rules[c[0]].is_mutex_with(&rbpa.rules[c[1]]) {
                Some((c[0], c[1]))
            } else {
                None
            }
        })
        .collect();
    println!("mutex_pairs {:?}", &mutex_pairs);
    let p = powerset(0..8, mutex_pairs.iter().copied());
    let mut guards: Vec<_> = p
        .into_iter()
        .map(|set| {
            let mut guard = HashMap::default();
            for &s in set.iter() {
                rbpa.rules[s].constrain_guard(&mut guard).expect("oops");
            }
            (set, guard)
        })
        .collect();
    for g in guards.iter() {
        println!("{:?}", g);
    }
    let mut to_drop = vec![];
    for g in guards.iter().enumerate().combinations(2) {
        let (ai, (ak, av)) = g[0];
        let (bi, (bk, bv)) = g[1];
        if av == bv {
        	if ak.len() > bk.len() {
        		to_drop.push(bi);
        		println!(
	                "({:?}) {:?} encompasses ({:?}) {:?}",
	                bk, bv, ak, av
	            );
        	} else {
        		to_drop.push(ai);
        		println!(
	                "({:?}) {:?} encompasses ({:?}) {:?}",
	                 ak, av, bk, bv,
	            );
        	}
        }
    }
    to_drop.sort();
    to_drop.dedup();
    for &d in to_drop.iter().rev() {
        guards.remove(d);
    }
    println!("============");
    for g in guards.iter() {
        println!("{:?}", g);
    }
}


fn powerset<I>(s: Range<LocId>, mutex_pairs: I) -> Vec<Vec<LocId>>
where
    I: IntoIterator<Item = (LocId, LocId)>,
{
    fn counter_contains(counter: usize, index: usize) -> bool {
        (counter >> index) % 2 == 0
    }

    // todo construct a proper datastructure here such that you can OR all at once
    let mut mask: Vec<_> = std::iter::repeat(0).take(s.len()).collect();
    for (mut a, mut b) in mutex_pairs.into_iter() {
        if a < b {
            std::mem::swap(&mut a, &mut b);
        }
        if a > b {
            mask[a] |= 1 << b;
        }
    }
    for (i, m) in mask.iter().enumerate() {
        println!("{} = {:b}", i, m);
    }

    let mut sets = vec![];
    let mut counter = 0;
    let counter_cap = 2usize.pow(s.len() as u32);
    while counter < counter_cap {
        println!("ctr... {}", counter);
        for a in (0..s.len()).rev() {
            if counter_contains(counter, a) {
                counter |= mask[a];
            }
        }
        let set = s
            .clone()
            .filter(|&x| counter_contains(counter, x))
            .collect();
        sets.push(set);
        counter += 1;
    }
    sets
}
