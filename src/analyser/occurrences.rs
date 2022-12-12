use std::collections::HashMap;

use crate::{
    ast::{Cm, Pil, Polynomial, ToPolynomial},
    visitor::{Result, Visitor},
};

#[derive(Default)]
pub struct OccurrenceCounter {
    occurrences: HashMap<Polynomial, (usize, usize)>,
}

impl OccurrenceCounter {
    pub fn count(pil: &Pil) -> Vec<(Polynomial, (usize, usize))> {
        let mut ranker = OccurrenceCounter::default();
        ranker.visit_pil(pil).unwrap();
        let mut res: Vec<_> = ranker.occurrences.drain().collect();
        res.sort_by(|(_, n0), (_, n1)| n0.partial_cmp(n1).unwrap());
        res
    }
}

impl Visitor for OccurrenceCounter {
    type Error = String;

    fn visit_cm(&mut self, cm: &Cm, ctx: &Pil) -> Result<Self::Error> {
        let pol = cm.to_polynomial(ctx);

        self.occurrences
            .entry(pol.polynomial().clone())
            .or_default();

        self.occurrences
            .entry(pol.polynomial().clone())
            .and_modify(|entry| {
                if pol.next {
                    entry.1 += 1;
                } else {
                    entry.0 += 1;
                }
            });
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::pilcom;

    use super::*;

    #[test]
    fn rank_adder() {
        let pil: Pil = serde_json::from_str(&pilcom("pil/adder.pil").unwrap()).unwrap();

        println!("occurrences {:#?}", &OccurrenceCounter::count(&pil));
    }
}
