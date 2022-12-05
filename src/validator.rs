use crate::{
    ast::{Pil, Reference},
    visitor::*,
};

#[derive(Default)]
pub struct Validator {
    constant_count: usize,
    commited_count: usize,
    complex_count: usize,
}

impl Visitor for Validator {
    type Error = String;

    fn visit_pil(&mut self, p: &Pil) -> Result<Self::Error> {
        visit_pil(self, p)?;
        if self.commited_count != p.n_commitments {
            return Err(format!(
                "Number of commitments doesn't match metadata: expected {} but found {}",
                p.n_commitments, self.commited_count
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

    fn visit_reference(&mut self, r: &Reference, _: &Pil) -> Result<Self::Error> {
        match r {
            Reference::ConstP(_) => {
                self.constant_count += 1;
            }
            Reference::CmP(_) => {
                self.commited_count += 1;
            }
            Reference::ImP(_) => {
                self.complex_count += 1;
            }
        };

        Ok(())
    }
}
