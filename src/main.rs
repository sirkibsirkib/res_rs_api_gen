use cascade::cascade;
use reo_rs::rbpa::RbpaRule;
use std::fmt;
use std::io::Write;

use reo_rs::rbpa::StatePred;

use hashbrown::HashMap;
use reo_rs::proto::traits::Proto;

use reo_rs::set;
use reo_rs::LocId;

static PREAMBLE: &'static str = r#"use reo_rs::tokens::{decimal::*, *};

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

impl<Q> Discerning for State<Q> where Self: Ruled<E0> {
    type List = <Self as Ruled<E0>>::Suffix;
}

pub trait Ruled<D: Decimal> {
    type Suffix: Sized;
}

"#;

fn main() -> std::io::Result<()> {
    let port_set = set! {0,1};
    let mut stdout = std::io::stdout();

    let proto_def = reo_rs_proto::Fifo3::<()>::proto_def();
    let rbpa = cascade! {
        proto_def.new_rbpa(&port_set).expect("Rbpa Creation error!");
        ..normalize();
    };
    let mem_locs_used = cascade! {
        rbpa
            .rules
            .iter()
            .flat_map(|r| r.get_guard().keys().copied())
            .collect::<Vec<_>>();
        ..sort();
        ..dedup();
    };

    let meta = RbpaMetadata {
        state_arity: mem_locs_used.len(),
        state_idx_to_proto_id: mem_locs_used.into_iter().enumerate().collect(),
        num_rules: rbpa.rules.len(),
    };

    write!(stdout, "{}", PREAMBLE)?;
    write!(stdout, "//////////// RULES ///////////////")?;
    for (rule_id, rule) in rbpa.rules.iter().enumerate() {
        write!(
            stdout,
            "{}",
            Rule {
                rule_id,
                rule,
                meta: &meta,
            }
        )?;
    }
    Ok(())
}

enum LocIdType {
    Putter,
    Getter,
    Mem,
}

struct RbpaMetadata {
    state_idx_to_proto_id: HashMap<LocId, LocId>,
    num_rules: usize,
    state_arity: usize,
}

struct Rule<'a> {
    rule_id: usize,
    rule: &'a RbpaRule,
    meta: &'a RbpaMetadata,
}
impl<'a> fmt::Display for Rule<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // let mut all_vars_buf = String::new();
        let Rule {
            rule,
            rule_id,
            meta,
        } = self;
        let rule_id = *rule_id;

        // first line comment
        let guard_pred = Pred {
            pred: rule.get_guard(),
            meta,
        };
        let assign_pred = Pred {
            pred: rule.get_assign(),
            meta,
        };
        write!(
            f,
            "//________ Rule {:0>6} __________________________________\n// POS: {} -{:->6}---> {}\n",
            rule_id,
            guard_pred,
            self.port(),
            assign_pred,
        )?;
        self.display_check(f)?;
        self.display_pos(f)?;

        for (&i, mi) in meta.state_idx_to_proto_id.iter() {
            if let Some(&b) = rule.get_guard().get(mi) {
                self.display_neg(f, i, b)?;
            }
        }
        write!(f, "\n")?;
        Ok(())
    }
}
impl<'a> Rule<'a> {
    fn port(&self) -> LocId {
        self.rule.get_port().expect("No port!")
    }
    fn rule_is_last(&self) -> bool {
        self.rule_id == self.meta.num_rules - 1
    }
    fn display_neg(&self, f: &mut fmt::Formatter, i: LocId, to_mismatch: bool) -> fmt::Result {
        let meta = self.meta;
        let rule_id = self.rule_id;

        write!(f, "// NEG: ")?;
        for _ in 0..i {
            write!(f, ".")?;
        }
        match to_mismatch {
            true => write!(f, "F"),
            false => write!(f, "T"),
        }?;
        for _ in (i + 1)..meta.state_arity {
            write!(f, ".")?;
        }
        write!(f, "\nimpl")?;

        let mismatch_var_seq = VarSeq {
            len: meta.state_arity,
            but: Some((i, !to_mismatch)),
        };

        if meta.state_arity > 0 {
            write!(f, "<{}>", &mismatch_var_seq)?;
        }
        write!(
            f,
            " Ruled<{}> for State<({})>\n",
            TypeDecimal(rule_id),
            &mismatch_var_seq
        )?;
        if !self.rule_is_last() {
            write!(
                f,
                "where State<({})>: Ruled<{}>,\n",
                &mismatch_var_seq,
                TypeDecimal(rule_id + 1)
            )?;
        }
        write!(f, "{{\n\ttype Suffix = ")?;
        if self.rule_is_last() {
            write!(f, "();\n")
        } else {
            write!(
                f,
                "<State<({})> as Ruled<{}>>::Suffix;\n",
                &mismatch_var_seq,
                TypeDecimal(rule_id)
            )
        }?;
        write!(f, "}}\n\n")?;
        Ok(())
    }

    fn display_checkable(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let pure_var_seq = VarSeq {
            len: self.meta.state_arity,
            but: None,
        };
        write!(f, "impl")?;
        if self.meta.state_arity > 0 {
            write!(f, "<{}>", &pure_var_seq)?;
        }
        write!(
            f,
            " Checkable<{}> for State<({})> {{\n\t",
            TypeDecimal(self.rule_id),
            &pure_var_seq,
        )?;
        self.display_checker_const(f)?;
        write!(f, "\n}}\n")?;
        Ok(())
    }

    fn display_pos(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let meta = &self.meta;
        let rule_id = self.rule_id;
        let rule = self.rule;
        let guard = rule.get_guard();
        let assign = rule.get_assign();

        write!(f, "impl")?;
        let pure_var_seq = VarSeq {
            len: meta.state_arity,
            but: None,
        };
        if meta.state_arity > 0 {
            write!(f, "<{}>", &pure_var_seq)?;
        }
        write!(
            f,
            " Ruled<{}> for State<({})>\nwhere\n",
            TypeDecimal(rule_id),
            &pure_var_seq,
        )?;
        for (i, mi) in meta.state_idx_to_proto_id.iter() {
            match rule.get_guard().get(mi) {
                None => (),
                Some(true) => write!(f, "\tV{}: XOrT,\n", i)?,
                Some(false) => write!(f, "\tV{}: XOrF,\n", i)?,
            }
        }
        if !self.rule_is_last() {
            write!(
                f,
                "\tState<({})>: Ruled<{}>,",
                &pure_var_seq,
                TypeDecimal(rule_id + 1)
            )?;
        }
        write!(
            f,
            "{{\n\ttype Suffix = (\n\t\tBranch<{}, {}, State<(",
            TypeDecimal(rule_id),
            TypeDecimal(self.port())
        )?;
        for (&i, mi) in meta.state_idx_to_proto_id.iter() {
            if i > 0 {
                write!(f, ", ")?;
            }
            match assign.get(mi).or_else(|| guard.get(mi)) {
                None => write!(f, "V{}", i),
                Some(true) => write!(f, "T"),
                Some(false) => write!(f, "F"),
            }?;
        }

        if self.rule_is_last() {
            write!(f, ")>,\n\t\t(),\n\t);\n")
        } else {
            write!(
                f,
                ")>,\n\t\t<State<({})> as Ruled<{}>>::Suffix,\n\t);\n",
                &pure_var_seq,
                TypeDecimal(rule_id)
            )
        }?;
        write!(f, "}}\n")?;
        Ok(())
    }

    fn display_checker_const(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let guard = self.rule.get_guard();
        let assign = self.rule.get_assign();
        write!(f, "const PRED: &[u64] = &[")?;
        let mut start = 0;
        while start < self.meta.state_arity {
            let end = (start + 32).min(self.meta.state_arity);
            if end > start {
                if start > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "0b")?;
            }
            for i in (start..end).rev() {
                let mi = self.meta.state_idx_to_proto_id.get(&i).expect("KKx");
                let s = match assign.get(&mi).or_else(|| guard.get(&mi)) {
                    Some(true) => "01",
                    Some(false) => "10",
                    None => "00",
                };
                write!(f, "{}", s)?;
            }
            start += 32;
        }
        write!(f, "];")?;
        Ok(())
    }
}

struct VarSeq {
    len: usize,
    but: Option<(LocId, bool)>,
}
impl fmt::Display for VarSeq {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for i in 0..self.len {
            if i > 0 {
                write!(f, ", ")?;
            }
            if let Some((loc, b)) = self.but {
                if loc == i {
                    match b {
                        true => write!(f, "T"),
                        false => write!(f, "F"),
                    }?;
                    continue;
                }
            }
            write!(f, "V{}", i)?;
        }
        Ok(())
    }
}

struct TypeDecimal(usize);
impl fmt::Display for TypeDecimal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut decimal = self.0;
        let mut brackets = 0;
        while decimal > 10 {
            write!(f, "D{}<", decimal % 10)?;
            brackets += 1;
            decimal /= 10;
        }
        write!(f, "E{}", decimal)?;
        for _ in 0..brackets {
            write!(f, ">")?;
        }
        Ok(())
    }
}

struct Pred<'a> {
    pred: &'a StatePred,
    meta: &'a RbpaMetadata,
}
impl<'a> fmt::Display for Pred<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Pred { meta, pred } = self;
        for i in 0..meta.state_arity {
            let mi = meta.state_idx_to_proto_id.get(&i).expect("BAD MAP");
            match pred.get(mi) {
                None => write!(f, "."),
                Some(true) => write!(f, "T"),
                Some(false) => write!(f, "F"),
            }?;
        }
        Ok(())
    }
}
