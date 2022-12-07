use std::collections::BTreeSet;
use std::fmt;

use crate::ast::*;
use crate::smt::*;
use crate::visitor::*;

// known ranges
const RANGES: [(&str, usize); 2] = [
    ("Global.BYTE2", u16::MAX as usize),
    ("Global.BYTE", u8::MAX as usize),
];

pub struct SmtPil {
    pil: Pil,
}

impl SmtPil {
    pub fn new(pil: Pil) -> Self {
        Self { pil }
    }
}

pub struct SmtEncoder {
    pub smt: Vec<SMTStatement>,
    funs: Vec<SMTFunction>,
}

impl SmtEncoder {
    fn out(&mut self, statement: SMTStatement) {
        self.smt.push(statement);
    }
}

impl fmt::Display for SmtPil {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut encoder = SmtEncoder {
            smt: Vec::default(),
            funs: Vec::default(),
        };
        encoder.visit_pil(&self.pil)?;

        writeln!(
            f,
            "; Uncomment the line below to enable proofs\n;(set-option :produce-proofs true)"
        )?;
        writeln!(
            f,
            "{}",
            encoder
                .smt
                .iter()
                .map(|s| s.as_smt())
                .collect::<Vec<_>>()
                .join("\n")
        )?;

        writeln!(f, "(check-sat)\n(get-model)")?;

        Ok(())
    }
}

struct VariableCollector {
    vars: BTreeSet<(IndexedReferenceKey, bool)>,
}

impl VariableCollector {
    fn new() -> Self {
        Self {
            vars: BTreeSet::default(),
        }
    }
}

impl Visitor for VariableCollector {
    type Error = ();

    fn visit_cm(&mut self, cm: &Cm, ctx: &Pil) -> Result<Self::Error> {
        let (key, _) = ctx.get_cm_reference(cm);
        self.vars.insert((key, cm.next));
        Ok(())
    }

    fn visit_const(&mut self, c: &Const, ctx: &Pil) -> Result<Self::Error> {
        let (key, _) = ctx.get_const_reference(c);
        self.vars.insert((key, c.next));
        Ok(())
    }
}

// Some helpers.
impl SmtEncoder {
    fn key_to_smt_var(
        &self,
        key: &IndexedReferenceKey,
        next: bool,
        suffix: Option<String>,
    ) -> SMTVariable {
        let mut key = key.to_string().replace(['.', '['], "_").replace(']', "");
        if next {
            key = format!("{}_next", key);
        }
        if suffix.is_some() {
            key = format!("{}_{}", key, suffix.unwrap());
        }
        SMTVariable::new(key, SMTSort::Int)
    }

    fn constr_to_smt_function(&self, i: &PolIdentity, constr_idx: usize, ctx: &Pil) -> SMTFunction {
        let mut collector = VariableCollector::new();
        let constr = &ctx.expressions[i.e.0];
        collector.visit_expression(constr, ctx).unwrap();
        let smt_vars: Vec<_> = collector
            .vars
            .iter()
            .map(|(key, next)| self.key_to_smt_var(key, *next, None))
            .collect();
        SMTFunction::new(format!("constr_{}", constr_idx), SMTSort::Bool, smt_vars)
    }

    fn all_vars_from_key(&self, key: &IndexedReferenceKey) -> Vec<SMTVariable> {
        [false, true]
            .iter()
            .flat_map(|next| {
                (0..=2).map(|row| self.key_to_smt_var(key, *next, Some(format!("row{}", row))))
            })
            .collect()
    }
}

impl Visitor for SmtEncoder {
    type Error = std::fmt::Error;

    fn visit_pil(&mut self, p: &Pil) -> Result<Self::Error> {
        let ctx = p;

        // Here we declare all variables that are going to be used in the query.
        // Those are, for every committed polynomial `pol`:
        // - pol_row0
        // - pol_next_row0
        // - pol_row1
        // - pol_next_row1
        // - pol_row2
        // - pol_next_row2
        for key in p
            .references
            .iter()
            // go through all references and generate all polynomials, whether they are array elements or not
            .map(|(key, reference)| {
                (
                    key,
                    match reference {
                        Reference::CmP(r) => r.len,
                        Reference::ConstP(r) => r.len,
                        Reference::ImP(r) => r.len,
                    },
                )
            })
            .flat_map(|(key, len)| match len {
                // generate `n` keys for arrays of size `n`
                Some(len) => (0..len)
                    .map(|index| IndexedReferenceKey::array_element(key, index))
                    .collect(),
                // generate 1 key for non-array polynomials
                None => vec![IndexedReferenceKey::basic(key)],
            })
        {
            // ignore columns which are used in ranges
            if !RANGES.iter().any(|(k, _)| {
                // the polynomials in RANGE are not arrays
                IndexedReferenceKey::basic(&String::from(*k)) == key
            }) {
                self.all_vars_from_key(&key)
                    .into_iter()
                    .for_each(|var| self.out(declare_const(var)));
            }
        }

        for (index, identity) in p.plookup_identities.iter().enumerate() {
            self.visit_plookup_identity(identity, ctx, index)?;
        }

        for (index, identity) in p.permutation_identities.iter().enumerate() {
            self.visit_permutation_identity(identity, ctx, index)?;
        }

        for (index, identity) in p.connection_identities.iter().enumerate() {
            self.visit_connection_identity(identity, ctx, index)?;
        }

        for (index, identity) in p.pol_identities.iter().enumerate() {
            self.visit_polynomial_identity(identity, ctx, index)?;
        }

        Ok(())
    }

    fn visit_public_cell(&mut self, _cell: &PublicCell, _ctx: &Pil) -> Result<Self::Error> {
        unimplemented!("declaration of public values is not supported")
    }

    fn visit_polynomial_identity(
        &mut self,
        i: &PolIdentity,
        ctx: &Pil,
        idx: usize,
    ) -> Result<Self::Error> {
        let constr = &ctx.expressions[i.e.0];
        let expr = eq_zero(self.encode_expression(constr, ctx));
        let fun = self.constr_to_smt_function(i, idx, ctx);
        self.funs.push(fun.clone());
        let fun_def = define_fun(fun, expr);
        self.out(fun_def);
        Ok(())
    }

    fn visit_connection_identity(
        &mut self,
        i: &ConnectionIdentity,
        _: &Pil,
        _: usize,
    ) -> Result<Self::Error> {
        unimplemented!("Found connection identity {:?} which is not supported", i);
    }

    fn visit_permutation_identity(
        &mut self,
        i: &PermutationIdentity,
        _: &Pil,
        _: usize,
    ) -> Result<Self::Error> {
        unimplemented!("Found permutation identity {:?} which is not supported", i);
    }

    fn visit_plookup_identity(
        &mut self,
        i: &PlookupIdentity,
        ctx: &Pil,
        _: usize,
    ) -> Result<Self::Error> {
        if let Some(ref _id) = i.sel_f {
            unimplemented!("Selectors for 'from' not implemented: {}", i.to_string(ctx));
        }

        let keys = i.f.iter().map(|id| {
            let e = &ctx.expressions[id.0];

            match e {
                Expression::Cm(w) => {
                    let (key, _) = ctx.get_cm_reference(&w.inner);
                    key
                }
                _ => unimplemented!(
                    "Expression type not implemented for plookup identity: {}",
                    e.to_string(ctx)
                ),
            }
        });

        if let Some(ref _id) = i.sel_t {
            unimplemented!("Selectors for 'to' not implemented: {}", i.to_string(ctx));
        }

        let max = i.t.iter().map(|id| {
            let e = &ctx.expressions[id.0];

            match e {
                Expression::Const(w) => {
                    let (key, _) = ctx.get_const_reference(&w.inner);
                    RANGES
                        .iter()
                        .find(|(k, _)| key == IndexedReferenceKey::basic(&String::from(*k)))
                        .unwrap_or_else(|| panic!("const {} does not have a known range", key))
                        .1
                }
                _ => unimplemented!(),
            }
        });

        for (key, max) in keys.zip(max) {
            self.all_vars_from_key(&key)
                .into_iter()
                .for_each(|var| self.out(assert(and(ge(var.clone(), 0), le(var, max as u64)))));
        }

        Ok(())
    }
}

impl SmtEncoder {
    fn encode_expression(&self, e: &Expression, ctx: &Pil) -> SMTExpr {
        match e {
            /*
            Expression::Public(w) => {
            encode_public(&w.inner)
            }
            Expression::Neg(w) => {
            encode_neg(&w.inner)
            }
            Expression::Exp(w) => {
            encode_exp(&w.inner)
            }
            */
            Expression::Add(w) => self.encode_add(&w.inner, ctx),
            Expression::Sub(w) => self.encode_sub(&w.inner, ctx),
            Expression::Mul(w) => self.encode_mul(&w.inner, ctx),
            Expression::Cm(w) => self.encode_cm(&w.inner, ctx),
            Expression::Number(w) => self.encode_number(&w.inner),
            Expression::Const(w) => self.encode_const(&w.inner, ctx),
            _ => panic!(),
        }
    }

    fn encode_add(&self, expr: &Add, ctx: &Pil) -> SMTExpr {
        add(
            self.encode_expression(&expr.values[0], ctx),
            self.encode_expression(&expr.values[1], ctx),
        )
    }

    fn encode_sub(&self, expr: &Sub, ctx: &Pil) -> SMTExpr {
        sub(
            self.encode_expression(&expr.values[0], ctx),
            self.encode_expression(&expr.values[1], ctx),
        )
    }

    fn encode_mul(&self, expr: &Mul, ctx: &Pil) -> SMTExpr {
        mul(
            self.encode_expression(&expr.values[0], ctx),
            self.encode_expression(&expr.values[1], ctx),
        )
    }

    fn encode_cm(&self, expr: &Cm, ctx: &Pil) -> SMTExpr {
        let (key, _) = ctx.get_cm_reference(expr);
        self.key_to_smt_var(&key, expr.next, None).into()
    }

    fn encode_number(&self, n: &Number) -> SMTExpr {
        literal(n.value.clone(), SMTSort::Int)
    }

    fn encode_const(&self, c: &Const, ctx: &Pil) -> SMTExpr {
        let (key, _) = ctx.get_const_reference(c);
        self.key_to_smt_var(&key, c.next, None).into()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn encode_byte4() {
        let pil_str = std::fs::read_to_string("byte4.pil.json").unwrap();
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();

        let smt_pil = SmtPil::new(pil);

        println!("{}", smt_pil);
    }

    #[test]
    #[ignore]
    fn encode_arith() {
        let pil_str = std::fs::read_to_string("arith.pil.json").unwrap();
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();

        let smt_pil = SmtPil::new(pil);

        println!("{}", smt_pil);
    }
}
