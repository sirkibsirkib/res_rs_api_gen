use std::fmt::Write;
use hashbrown::HashSet;
use reo_rs::rbpa::StatePred;

use hashbrown::HashMap;
use reo_rs::proto::traits::Proto;

use reo_rs::set;
use reo_rs::LocId;

// use std::io::Write;
use itertools::Itertools;
// use num_bigint::BigUint;

static PREAMBLE: &'static str = 
r#"use reo_rs::tokens::{decimal::*, *};

pub trait XOrT {}
impl XOrT for T {}
impl XOrT for X {}

pub trait XOrF {}
impl XOrF for F {}
impl XOrF for X {}

pub trait Discerning: Token {
    type List: Sized;
    fn discern(self, proto: fn() -> usize) -> Discerned<Self::List>
    where
        Self: Ruled<E0>,
        Discerned<<Self as Ruled<E0>>::Suffix>: MayBranch,
    {
        let branching = <Discerned<<Self as Ruled<E0>>::Suffix> as MayBranch>::BRANCHING;
        let rule_id = if branching {
            proto()
        } else {
            !0 // bogus value
        };
        unsafe { std::mem::transmute(rule_id) }
    }
}

impl<Q> Discerning for State<Q where Self: Ruled<E0> {
    type List = <Self as Ruled<E0>>::Suffix;
}

pub trait Ruled<D: Decimal> {
    type Suffix: Sized;
}

//////////// RULES ///////////////
"#;


fn main() {
    let port_set = set! {0,1};

    let mut s = String::new();

    // 1. fetch the RBPA, projected onto your port set
    let mut rbpa = reo_rs_proto::Fifo3::<()>::proto_def()
        .new_rbpa(&port_set)
        .expect("WAH");
    println!("RBPA START: {:#?}", &rbpa);
    rbpa.normalize();

    let mut mem_locs_used: Vec<LocId> = rbpa.rules.iter().flat_map(|r| r.get_guard().keys().copied()).collect();
    mem_locs_used.sort();
    mem_locs_used.dedup();
    println!("mem_locs_used {:?}", &mem_locs_used);

    // let state_arity = mem_locs_used.len();
    let state_idx_to_proto_id: HashMap<LocId, LocId> = mem_locs_used.into_iter().enumerate().collect();
    println!("state_idx_to_proto_id {:?}", &state_idx_to_proto_id);

    let state_arity = state_idx_to_proto_id.len();


    write!(&mut s, "{}", PREAMBLE).unwrap();

    let mut all_vars_buf = String::new();
    for (rule_id, rule) in rbpa.rules.iter().enumerate() {

        // first line comment
        write!(&mut s, "//^^^^^^^^^ Rule {:0>6} ^^^^^^^^^//\n// POS: ", rule_id).unwrap();
        write_pred(&mut s, rule.get_guard(), &state_idx_to_proto_id);
        write!(&mut s, " -{:->6}---> ", rule.get_port().unwrap()).unwrap();
        write_pred(&mut s, rule.get_assign(), &state_idx_to_proto_id);

        all_vars_buf.clear();
        for i in 0..state_arity {
            if i > 0 {
                write!(&mut all_vars_buf, ", ").unwrap();
            }
            write!(&mut all_vars_buf, "V{}", i).unwrap();
        }

        write!(&mut s, "\nimpl").unwrap();
        if state_arity > 0 {
            write!(&mut s, "<{}>", &all_vars_buf).unwrap();
        }
        write!(&mut s, " Ruled<").unwrap();
        write_decimal(&mut s, rule_id);
        write!(&mut s, "> for State<({})>\nwhere\n", &all_vars_buf).unwrap();
        for (i, mi) in state_idx_to_proto_id.iter() {
            match rule.get_guard().get(mi) {
                None => (),
                Some(true) => write!(&mut s, "\tV{}: XOrT,\n", i).unwrap(),
                Some(false) => write!(&mut s, "\tV{}: XOrF,\n", i).unwrap(),
            }
        }
        let rule_is_last = rule_id == rbpa.rules.len() - 1;
        if !rule_is_last {
            write!(&mut s, "\tState<({})>: Ruled<,", &all_vars_buf).unwrap();
            write_decimal(&mut s, rule_id + 1);
            write!(&mut s, ">,\n").unwrap();
        }
        write!(&mut s, "{{\n\ttype Suffix = (\n\t\tBranch<").unwrap();
        write_decimal(&mut s, rule_id);
        write!(&mut s, ", ").unwrap();
        write_decimal(&mut s, rule.get_port().unwrap());
        write!(&mut s, ", State<(").unwrap();
        for (&i, mi) in state_idx_to_proto_id.iter() {
            if i > 0 {
                write!(&mut s, ", ").unwrap();
            }
            match rule.get_guard().get(mi).or_else(|| rule.get_assign().get(mi)) {
                None => write!(&mut s, "V{}", i).unwrap(),
                Some(true) => write!(&mut s, "T").unwrap(),
                Some(false) => write!(&mut s, "F").unwrap(),
            }
        }
        
        if rule_is_last {
            write!(&mut s, ")>,\n\t\t(),\n\t);").unwrap();
        } else {
            write!(&mut s, ")>,\n\t\t<State<({})> as Ruled<", &all_vars_buf).unwrap();
            write_decimal(&mut s, rule_id + 1);
            write!(&mut s, ">>::Suffix,\n\t);").unwrap();
        }
        write!(&mut s, "\n}}\n").unwrap();

        for (&i, mi) in state_idx_to_proto_id.iter() {
            if let Some(b) = rule.get_guard().get(mi) {
                write!(&mut s, "// NEG: ").unwrap();
                for _ in 0..i {
                    write!(&mut s, ".").unwrap();
                }
                match b {
                    true => write!(&mut s, "F").unwrap(),
                    false => write!(&mut s, "T").unwrap(),
                }
                for _ in (i+1)..state_arity {
                    write!(&mut s, ".").unwrap();
                }
                write!(&mut s, "\nimpl").unwrap();

                all_vars_buf.clear();
                for i2 in 0..state_arity {
                    if i2 > 0 {
                        write!(&mut all_vars_buf, ", ").unwrap();
                    }
                    if i == i2 {
                        match b {
                            true => write!(&mut all_vars_buf, "F").unwrap(),
                            false => write!(&mut all_vars_buf, "T").unwrap(),
                        }
                    } else {
                        write!(&mut all_vars_buf, "V{}", i2).unwrap();
                    }
                }
                if state_arity > 0 {
                    write!(&mut s, "<{}>", &all_vars_buf).unwrap();
                }
                write!(&mut s, " Ruled<").unwrap();
                write_decimal(&mut s, rule_id);
                write!(&mut s, "> for State<({})>\n", &all_vars_buf).unwrap();

            }
            if !rule_is_last {
                write!(&mut s, "where State<({})>: Ruled<", &all_vars_buf).unwrap();
                write_decimal(&mut s, rule_id + 1);
                write!(&mut s, ">,\n").unwrap();
            }
            write!(&mut s, "{{\n\ttype Suffix = ").unwrap();
            if rule_is_last {

                write!(&mut s, "(Branch<").unwrap();
                write_decimal(&mut s, rule_id);
                write!(&mut s, ", ").unwrap();
                write_decimal(&mut s, rule.get_port().unwrap());
                write!(&mut s, ", State<({})>, ());\n", &all_vars_buf).unwrap();

            } else {
                write!(&mut s, "();\n").unwrap();
            }
            write!(&mut s, "}}\n\n").unwrap();
        }
        write!(&mut s, "\n").unwrap();
    }


    println!("S::::\n{}", s);

    // 2. normalize RBPA (removing silent transitions)
}

fn write_decimal(s: &mut String, mut decimal: usize) {
    let mut brackets = 0;
    while decimal > 10 {
        write!(s, "D{}<", decimal % 10).unwrap();
        brackets += 1;
        decimal /= 10;
    }
    write!(s, "E{}", decimal).unwrap();
    for _ in 0..brackets {
        write!(s, ">").unwrap();
    }
}


fn write_pred(s: &mut String, pred: &StatePred, state_idx_to_proto_id: &HashMap<LocId, LocId>) {
    let state_arity = state_idx_to_proto_id.len();
    for i in 0..state_arity {
        let mi = state_idx_to_proto_id.get(&i).unwrap();
        match pred.get(mi) {
            None => write!(s, ".").unwrap(),
            Some(true) => write!(s, "T").unwrap(),
            Some(false) => write!(s, "F").unwrap(),
        }
    }
}