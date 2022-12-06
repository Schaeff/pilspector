use std::fmt;

use crate::{
    ast::{ConnectionIdentity, Expression, PermutationIdentity, Pil, PlookupIdentity, PublicCell},
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

pub struct SmtEncoder<'a, 'b> {
    pub f: &'a mut fmt::Formatter<'b>,
}

impl fmt::Display for SmtPil {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut encoder = SmtEncoder { f };
        encoder.visit_pil(&self.pil)
    }
}

impl<'a, 'b> Visitor for SmtEncoder<'a, 'b> {
    type Error = std::fmt::Error;

    fn visit_pil(&mut self, p: &Pil) -> Result<Self::Error> {
        let ctx = p;

        writeln!(self.f, "(set-option :produce-proofs true)")?;

        writeln!(self.f)?;

        for key in p.references.keys() {
            // ignore columns which are used in ranges
            if !RANGES.iter().any(|(k, _)| k == key) {
                let key = key.clone().replace('.', "_");
                writeln!(self.f, "(declare-const {} Int)", key)?;
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

            writeln!(
                self.f,
                r#"
(assert (and
    (>= {} 0)
    (<= {} {})
))"#,
                key, key, max
            )?;
        }

        Ok(())
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