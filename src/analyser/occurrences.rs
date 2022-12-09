use std::collections::HashMap;

use crate::{
    ast::{Cm, Name, Pil, ToPolynomial},
    visitor::{Result, Visitor},
};

#[derive(Default)]
pub struct OccurrenceCounter {
    occurrences: HashMap<Name, usize>,
}

impl OccurrenceCounter {
    pub fn count(pil: &Pil) -> String {
        let mut ranker = OccurrenceCounter::default();
        ranker.visit_pil(pil).unwrap();
        let mut res: Vec<_> = ranker.occurrences.drain().collect();
        res.sort_by(|(_, n0), (_, n1)| n0.partial_cmp(n1).unwrap());
        res.iter()
            .map(|(name, count)| format!("{} : {}", name, count))
            .collect::<Vec<_>>()
            .join("\n")
    }
}

impl Visitor for OccurrenceCounter {
    type Error = String;

    fn visit_cm(&mut self, cm: &Cm, ctx: &Pil) -> Result<Self::Error> {
        *self
            .occurrences
            .entry(cm.to_polynomial(ctx).to_string())
            .or_insert(0) += 1;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn rank_adder() {
        let pil_str = std::fs::read_to_string("main.pil.json").unwrap();
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();

        println!("occurrences {:#?}", &OccurrenceCounter::count(&pil)[0..50]);
    }
}
