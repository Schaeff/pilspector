use crate::{
    ast::{ExpressionId, Pil, Polynomials, PublicCell},
    visitor::*,
};

#[derive(Default)]
pub struct Validator {
    constant_count: usize,
    commited_count: usize,
    intermediate_count: usize,
}

impl Visitor for Validator {
    type Error = String;

    fn visit_expression_id(&mut self, id: &ExpressionId, ctx: &Pil) -> Result<Self::Error> {
        if id.0 >= ctx.expressions.len() {
            return Err("Expression index out of bounds".into());
        }
        visit_expression_id(self, id, ctx)
    }

    fn visit_pil(&mut self, p: &Pil) -> Result<Self::Error> {
        visit_pil(self, p)?;
        if self.commited_count != p.n_commitments {
            return Err(format!(
                "Number of commitments doesn't match metadata: expected {} but found {}",
                p.n_commitments, self.commited_count
            ));
        }
        if self.intermediate_count != p.n_im {
            return Err(format!(
                "Number of intermediates doesn't match metadata: expected {} but found {}",
                p.n_im, self.intermediate_count
            ));
        }
        if self.constant_count != p.n_constants {
            return Err(format!(
                "Number of constants doesn't match metadata: expected {} but found {}",
                p.n_constants, self.constant_count
            ));
        }
        Ok(())
    }

    fn visit_public_cell(&mut self, cell: &PublicCell, _: &Pil) -> Result<Self::Error> {
        if cell.pol_type != "cmP" {
            return Err(format!(
                "Expected the public cell to reference a committed polynomial, found {}",
                cell.pol_type
            ));
        }
        Ok(())
    }

    fn visit_reference(&mut self, r: &Polynomials, _: &Pil) -> Result<Self::Error> {
        match r {
            Polynomials::ConstP(r) => {
                self.constant_count += r.len.unwrap_or(1);
            }
            Polynomials::CmP(r) => {
                self.commited_count += r.len.unwrap_or(1);
            }
            Polynomials::ImP(r) => {
                self.intermediate_count += r.len.unwrap_or(1);
            }
        };

        Ok(())
    }
}
