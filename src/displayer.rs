use crate::{
    ast::{
        Add, Cm, ConnectionIdentity, Const, Mul, Number, PermutationIdentity, Pil, PlookupIdentity,
        PolIdentity, PublicCell, Reference, ReferenceKey, Sub,
    },
    visitor::*,
};

use std::io::Write;

#[derive(Default)]
pub struct PilDisplayer {
    pub f: Vec<u8>,
}

impl Visitor for PilDisplayer {
    type Error = std::io::Error;

    fn visit_public_cell(&mut self, cell: &PublicCell, ctx: &Pil) -> Result<Self::Error> {
        write!(self.f, "public ")?;
        write!(self.f, "{}", cell.name)?;
        write!(self.f, " = ")?;

        self.visit_cm(
            &Cm {
                id: cell.pol_id,
                next: false,
            },
            ctx,
        )?;

        writeln!(self.f, "[{}];", cell.idx.0)
    }

    fn visit_pil(&mut self, p: &Pil) -> Result<Self::Error> {
        let ctx = p;

        for public_cell in &p.publics {
            self.visit_public_cell(public_cell, ctx)?;
        }

        for (key, r) in &p.references {
            write!(self.f, "pol")?;

            let size = match r {
                Reference::CmP(r) => {
                    write!(self.f, " commit")?;
                    r.len
                }
                Reference::ConstP(r) => {
                    write!(self.f, " constant")?;
                    r.len
                }
                Reference::ImP(r) => {
                    write!(self.f, "")?;
                    r.len
                }
            };

            write!(self.f, " ")?;

            write!(self.f, "{}", key)?;

            if let Some(size) = size {
                write!(self.f, "[{}]", size)?;
            }

            if let Reference::ImP(r) = r {
                write!(self.f, " == ")?;
                self.visit_expression(&p.expressions[r.id.0], ctx)?;
            }

            writeln!(self.f, ";")?;
        }

        for i in &p.pol_identities {
            self.visit_polynomial_identity(i, ctx)?;
            writeln!(self.f)?;
        }

        for i in &p.plookup_identities {
            self.visit_plookup_identity(i, ctx)?;
            writeln!(self.f)?;
        }

        for i in &p.permutation_identities {
            self.visit_permutation_identity(i, ctx)?;
            writeln!(self.f)?;
        }

        for i in &p.connection_identities {
            self.visit_connection_identity(i, ctx)?;
            writeln!(self.f)?;
        }

        Ok(())
    }

    fn visit_polynomial_identity(&mut self, i: &PolIdentity, ctx: &Pil) -> Result<Self::Error> {
        self.visit_expression(&ctx.expressions[i.e.0], ctx)?;
        write!(self.f, " == 0")
    }

    fn visit_plookup_identity(&mut self, i: &PlookupIdentity, ctx: &Pil) -> Result<Self::Error> {
        if let Some(ref id) = i.sel_f {
            self.visit_expression_id(id, ctx)?;
            write!(self.f, " * ")?;
        }

        write!(self.f, "[ ")?;

        for id in &i.f {
            self.visit_expression_id(id, ctx)?;
            write!(self.f, ", ")?;
        }

        write!(self.f, "]")?;

        write!(self.f, " in ")?;

        if let Some(ref id) = i.sel_t {
            self.visit_expression_id(id, ctx)?;
            write!(self.f, " * ")?;
        }

        write!(self.f, "[ ")?;

        for id in &i.t {
            self.visit_expression_id(id, ctx)?;
            write!(self.f, ", ")?;
        }

        write!(self.f, "]")?;

        Ok(())
    }

    fn visit_permutation_identity(
        &mut self,
        i: &PermutationIdentity,
        ctx: &Pil,
    ) -> Result<Self::Error> {
        if let Some(ref id) = i.sel_f {
            self.visit_expression_id(id, ctx)?;
            write!(self.f, " * ")?;
        }

        write!(self.f, "[ ")?;

        for id in &i.f {
            self.visit_expression_id(id, ctx)?;
            write!(self.f, ", ")?;
        }

        write!(self.f, "]")?;

        write!(self.f, " is ")?;

        if let Some(ref id) = i.sel_t {
            self.visit_expression_id(id, ctx)?;
            write!(self.f, " * ")?;
        }

        write!(self.f, "[ ")?;

        for id in &i.t {
            self.visit_expression_id(id, ctx)?;
            write!(self.f, ", ")?;
        }

        write!(self.f, "]")?;

        Ok(())
    }

    fn visit_connection_identity(
        &mut self,
        i: &ConnectionIdentity,
        ctx: &Pil,
    ) -> Result<Self::Error> {
        write!(self.f, "[ ")?;

        for id in &i.pols {
            self.visit_expression_id(id, ctx)?;
            write!(self.f, ", ")?;
        }

        write!(self.f, "]")?;

        write!(self.f, " connect ")?;

        write!(self.f, "[ ")?;

        for id in &i.connections {
            self.visit_expression_id(id, ctx)?;
            write!(self.f, ", ")?;
        }

        write!(self.f, "]")?;

        Ok(())
    }

    fn visit_reference_key(&mut self, c: &ReferenceKey, _ctx: &Pil) -> Result<Self::Error> {
        write!(self.f, "{}", c)
    }

    fn visit_add(&mut self, add: &Add, ctx: &Pil) -> Result<Self::Error> {
        write!(self.f, "(")?;
        self.visit_expression(&add.values[0], ctx)?;
        write!(self.f, " + ")?;
        self.visit_expression(&add.values[1], ctx)?;
        write!(self.f, ")")
    }

    fn visit_sub(&mut self, sub: &Sub, ctx: &Pil) -> Result<Self::Error> {
        write!(self.f, "(")?;
        self.visit_expression(&sub.values[0], ctx)?;
        write!(self.f, " - ")?;
        self.visit_expression(&sub.values[1], ctx)?;
        write!(self.f, ")")
    }

    fn visit_mul(&mut self, mul: &Mul, ctx: &Pil) -> Result<Self::Error> {
        write!(self.f, "(")?;
        self.visit_expression(&mul.values[0], ctx)?;
        write!(self.f, " * ")?;
        self.visit_expression(&mul.values[1], ctx)?;
        write!(self.f, ")")
    }

    fn visit_number(&mut self, c: &Number, _ctx: &Pil) -> Result<Self::Error> {
        write!(self.f, "{}", c.value)
    }

    fn visit_next(&mut self, next: &bool, _ctx: &Pil) -> Result<Self::Error> {
        if *next {
            write!(self.f, "'")?;
        }
        Ok(())
    }
}
