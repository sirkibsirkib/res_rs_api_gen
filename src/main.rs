use hashbrown::{HashMap, HashSet};
use reo_rs::proto::traits::Proto;
use reo_rs::rbpa::Rbpa;
use reo_rs::LocId;
use reo_rs::{map, set};
use std::ops::Range;
// use std::io::Write;

fn main() {
    let port_set = set! {0, 1};
    let _out = String::new();
    let mut rbpa = reo_rs_proto::Fifo3::<()>::proto_def()
        .new_rbpa(&port_set)
        .expect("WAH");
    rbpa.normalize();
    use itertools::Itertools;
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
    let p = powerset(0..8, mutex_pairs.iter().copied());
    let mut guard = HashMap::default();
    for set in p.iter() {
        for &s in set.iter() {
            rbpa.rules[s].constrain_guard(&mut guard).expect("oops");
        }
        print!("set: {:?} guard:\t", set);
        let mut buf = vec!['.'; 5];
        for (&k, &v) in guard.iter() {
            if buf.len() <= k {
                buf.resize_with(k + 1, || '.');
            }
            buf[k] = if v { 'T' } else { 'F' };
        }
        for b in buf.drain(..) {
            print!("{}", b);
        }
        println!();
        guard.clear();
    }
}

// fn compute_mutex_pairs(rbpa: &Rbpa) -> HashMap<LocId, HashSet<LocId>> {
//     let num_rules = rbpa.rules.len();
//     assert!(num_rules > 0);
//     let mut mutex_pairs = HashMap::<LocId, HashSet<LocId>>::default();
//     for i in 0..(num_rules - 1) {
//         for j in (i + 1)..num_rules {
//             if rbpa.rules[j].is_mutex_with(&rbpa.rules[i]) {
//                 mutex_pairs
//                     .entry(j)
//                     .or_insert_with(HashSet::default)
//                     .insert(i);
//             }
//         }
//     }
//     mutex_pairs
// }

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
        for a in 0..s.len() {
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
