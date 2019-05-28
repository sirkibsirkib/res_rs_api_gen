use hashbrown::HashMap;
use reo_rs::proto::traits::Proto;

use reo_rs::set;
use reo_rs::LocId;
use std::ops::Range;
// use std::io::Write;
use itertools::Itertools;
use num_bigint::BigUint;

fn main() {
    let port_set = set! {0, 1};
    let _out = String::new();
    let mut rbpa = reo_rs_proto::Fifo3::<()>::proto_def()
        .new_rbpa(&port_set)
        .expect("WAH");
    rbpa.normalize();
    let mutex_pairs: Vec<[LocId;2]> = (0..rbpa.rules.len())
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
                println!("({:?}) {:?} encompasses ({:?}) {:?}", bk, bv, ak, av);
            } else {
                to_drop.push(ai);
                println!("({:?}) {:?} encompasses ({:?}) {:?}", ak, av, bk, bv,);
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

/// Given an end to a range of port ids (presuming port range 0..`rng_end`) and
/// a list of ids whose guards render them mutually-exclusively applicable to
/// states (eg: TTT and FXX).
///
/// It produces the powerset construction of these port IDs, omitting any sets
/// that contain both elements of any mutex pair.
fn powerset<I>(rng_end: LocId, mutex_pairs: I) -> Vec<Vec<LocId>>
where
    I: IntoIterator<Item = [LocId;2]>,
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

#[test]
pub fn bigint() {
    let mut b = num_bigint::BigUint::new(vec![1]);
    b <<= 2374;
    let mut dec = num_bigint::BigUint::new(vec![1]);
    dec <<= 2342;
    while b > dec {
        println!("{:?},", b);
        b ^= &dec;
    }
    println!("{:?}", b);
}
