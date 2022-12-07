use std::fmt;

use crate::{
    ast::*,//{ConnectionIdentity, Expression, PermutationIdentity, Pil, PlookupIdentity, PolIdentity, PublicCell},
    smt::*,
    visitor::*,
};

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

impl Visitor for SmtEncoder {
    type Error = std::fmt::Error;

    fn visit_pil(&mut self, p: &Pil) -> Result<Self::Error> {
        let ctx = p;

        for key in p.references.keys() {
            // ignore columns which are used in ranges
            if !RANGES.iter().any(|(k, _)| k == key) {
                let key = key.clone().replace('.', "_");
                self.out(declare_const(SMTVariable::new(key, SMTSort::Int)));
            }
        }

        for i in &p.pol_identities {
            self.visit_polynomial_identity(i, ctx)?;
        }

        for i in &p.plookup_identities {
            self.visit_plookup_identity(i, ctx)?;
        }

        for i in &p.permutation_identities {
            self.visit_permutation_identity(i, ctx)?;
        }

        for i in &p.connection_identities {
            self.visit_connection_identity(i, ctx)?;
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
    ) -> Result<Self::Error> {
        let constr = &ctx.expressions[i.e.0];
        let expr = eq_zero(self.encode_expression(constr, ctx));
        let fun = define_fun(SMTVariable::new(format!("constr_{}", 1).to_string(), SMTSort::Bool), vec![], expr);
        println!("{}", fun.as_smt());
        unimplemented!("Found polynomial identity {:?} which is not supported", i);
    }

    fn visit_connection_identity(
        &mut self,
        i: &ConnectionIdentity,
        _: &Pil,
    ) -> Result<Self::Error> {
        unimplemented!("Found connection identity {:?} which is not supported", i);
    }

    fn visit_permutation_identity(
        &mut self,
        i: &PermutationIdentity,
        _: &Pil,
    ) -> Result<Self::Error> {
        unimplemented!("Found permutation identity {:?} which is not supported", i);
    }

    fn visit_plookup_identity(&mut self, i: &PlookupIdentity, ctx: &Pil) -> Result<Self::Error> {
        if let Some(ref _id) = i.sel_f {
            unimplemented!();
        }

        let keys = i.f.iter().map(|id| {
            let e = &ctx.expressions[id.0];

            match e {
                Expression::Cm(w) => {
                    let (key, _) = ctx.get_cm_reference(&w.inner);
                    key
                }
                _ => unimplemented!(),
            }
        });

        if let Some(ref _id) = i.sel_t {
            unimplemented!()
        }

        let max = i.t.iter().map(|id| {
            let e = &ctx.expressions[id.0];

            match e {
                Expression::Const(w) => {
                    let (key, _) = ctx.get_const_reference(&w.inner);
                    RANGES
                        .iter()
                        .find(|(k, _)| key == k)
                        .unwrap_or_else(|| panic!("const {} does not have a known range", key))
                        .1
                }
                _ => unimplemented!(),
            }
        });

        for (key, max) in keys.zip(max) {
            let key = key.clone().replace('.', "_");
            let var = SMTVariable::new(key, SMTSort::Int);

            self.out(assert(and(ge(var.clone(), 0), le(var, max as u64))));
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
            Expression::Add(w) => {
                self.encode_add(&w.inner, ctx)
            },
            Expression::Sub(w) => {
                self.encode_sub(&w.inner, ctx)
            },
            Expression::Mul(w) => {
                self.encode_mul(&w.inner, ctx)
            },
            Expression::Cm(w) => {
                self.encode_cm(&w.inner, ctx)
            },
            Expression::Number(w) => {
                self.encode_number(&w.inner)
            },
            Expression::Const(w) => {
                self.encode_const(&w.inner, ctx)
            },
            _ => panic!()
        }
    }

    fn encode_add(&self, expr: &Add, ctx: &Pil) -> SMTExpr {
        add(
            self.encode_expression(&expr.values[0], ctx),
            self.encode_expression(&expr.values[1], ctx)
           )
    }

    fn encode_sub(&self, expr: &Sub, ctx: &Pil) -> SMTExpr {
        sub(
            self.encode_expression(&expr.values[0], ctx),
            self.encode_expression(&expr.values[1], ctx)
           )
    }

    fn encode_mul(&self, expr: &Mul, ctx: &Pil) -> SMTExpr {
        mul(
            self.encode_expression(&expr.values[0], ctx),
            self.encode_expression(&expr.values[1], ctx)
           )
    }

    fn encode_cm(&self, expr: &Cm, ctx: &Pil) -> SMTExpr {
        let (key, _) = ctx.get_cm_reference(expr);
        let key = key.clone().replace('.', "_");
        SMTVariable::new(key, SMTSort::Int).into()
    }

    fn encode_number(&self, n: &Number) -> SMTExpr {
        literal(n.value.clone(), SMTSort::Int)
    }

    fn encode_const(&self, c: &Const, ctx: &Pil) -> SMTExpr {
        let (key, _) = ctx.get_const_reference(&c);
        let key = key.clone().replace('.', "_");
        SMTVariable::new(key, SMTSort::Int).into()
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
}
