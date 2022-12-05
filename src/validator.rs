use crate::{visitor::*, ast::{Pil, ReferenceType}};

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
            return Err(format!("Number of commitments doesn't match metadata"));
        }
        if self.constant_count != p.n_constants {
            return Err(format!("Number of constants doesn't match metadata"));
        }
        Ok(())
    }

    fn visit_reference_type(&mut self, t: &ReferenceType, _: &Pil) -> Result<Self::Error> {
        match t {
            ReferenceType::ConstP => {
                self.constant_count += 1;
            },
            ReferenceType::CmP => {
                self.commited_count += 1;
            },
            ReferenceType::ImP => {
                self.complex_count += 1;
            },
        }
        Ok(())
    }
}