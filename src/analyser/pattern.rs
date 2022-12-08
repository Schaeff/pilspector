use std::collections::HashMap;

use crate::{
    ast::{Expression, Pil, PolIdentity, IndexedReferenceKey, ExpressionWrapper, Add, Sub, Neg, Mul, ToStringWithContext},
    displayer::PilDisplayer,
    visitor::{Result, Visitor}, pilcom_from_str,
};

pub struct PatternDetector {
    pil: Pil,
    pattern_pil: Pil,
    pattern: Expression,
    occurrences: Vec<Expression>,
}

impl PatternDetector {
    pub fn detect(pil: &Pil, pattern_pil: &Pil) -> String {

        let expression = pattern_pil.get_expression(&pattern_pil.pol_identities[0].e);

        let mut detector = PatternDetector {
            pattern: expression.clone(),
            occurrences: vec![],
            pil: pil.clone(),
            pattern_pil: pattern_pil.clone(),
        };
        detector.visit_pil(&pil).unwrap();

        detector
            .occurrences
            .iter()
            .map(|e| {
                let mut displayer = PilDisplayer::default();
                displayer.visit_expression(e, &pil).unwrap();
                String::from_utf8(displayer.f).unwrap()
            })
            .collect::<Vec<_>>()
            .join("\n")
    }

    fn matches(&self, e: &Expression) -> bool {
        e.matches(&self.pattern, &self.pil, &self.pattern_pil, HashMap::default()).0
    }
}

trait Matches {
    fn matches(&self, pattern: &Self, ctx: &Pil, pattern_ctx: &Pil, bindings: HashMap<IndexedReferenceKey, Expression>) -> (bool, HashMap<IndexedReferenceKey, Expression>);
}

impl Matches for Expression {
    fn matches(&self, pattern: &Expression, ctx: &Pil, pattern_ctx: &Pil, mut bindings: HashMap<IndexedReferenceKey, Expression>) -> (bool, HashMap<IndexedReferenceKey, Expression>) {      
        println!("try match {} to {}", self.to_string(ctx), pattern.to_string(pattern_ctx));
        println!("{}", bindings.iter().map(|(key, value)| format!("{} -> {}", key.to_string(), value.to_string(ctx))).collect::<Vec<_>>().join(", "));
  
        match (self, pattern) {
            (e, Expression::Cm(cm)) => {
                let pol = pattern_ctx.get_cm_reference(&cm.inner).0;
                let (res, to_insert) = match bindings.get(&pol) {
                    Some(bound_e) => (e == bound_e, None),
                    None => (true, Some(e))
                };

                bindings.extend(to_insert.map(|e| (pol, e.clone())));
                (res, bindings)
            },
            (Expression::Add(left), Expression::Add(right)) => {
                left.matches(right, ctx, pattern_ctx, bindings)
            },
            (Expression::Sub(left), Expression::Sub(right)) => {
                left.matches(right, ctx, pattern_ctx, bindings)
            },
            (Expression::Neg(left), Expression::Neg(right)) => {
                left.matches(right, ctx, pattern_ctx, bindings)
            },
            (Expression::Mul(left), Expression::Mul(right)) => {
                left.matches(right, ctx, pattern_ctx, bindings)
            },
            (Expression::Number(_), Expression::Number(_)) => (true, bindings),
            (Expression::Const(_), Expression::Const(_)) => (true, bindings),
            (e, p) => {
                println!("failed to match {} to {}", e.to_string(ctx), p.to_string(pattern_ctx));
                (false, bindings)
            }
        }
    }
}

impl<E: Matches> Matches for ExpressionWrapper<E> {
    fn matches(&self, pattern: &Self, ctx: &Pil, pattern_ctx: &Pil, bindings: HashMap<IndexedReferenceKey, Expression>) -> (bool, HashMap<IndexedReferenceKey, Expression>) {
        self.inner.matches(&pattern.inner, ctx, pattern_ctx, bindings)
    }
}

impl Matches for Add {
    fn matches(&self, pattern: &Self, ctx: &Pil, pattern_ctx: &Pil, bindings: HashMap<IndexedReferenceKey, Expression>) -> (bool, HashMap<IndexedReferenceKey, Expression>) {
        let (left_match, bindings) = self.values[0].matches(&pattern.values[0], ctx, pattern_ctx, bindings);
        if !left_match {
            let (left_match, bindings) = self.values[0].matches(&pattern.values[1], ctx, pattern_ctx, bindings);
            if !left_match {
                return (false, bindings)
            }
            self.values[1].matches(&pattern.values[0], ctx, pattern_ctx, bindings)
        } else {
            self.values[1].matches(&pattern.values[1], ctx, pattern_ctx, bindings)
        }
    }
}

impl Matches for Sub {
    fn matches(&self, pattern: &Self, ctx: &Pil, pattern_ctx: &Pil, bindings: HashMap<IndexedReferenceKey, Expression>) -> (bool, HashMap<IndexedReferenceKey, Expression>) {
        let (left_match, bindings) = self.values[0].matches(&pattern.values[0], ctx, pattern_ctx, bindings);
        if !left_match {
            return (false, bindings);
        }
        self.values[1].matches(&pattern.values[1], ctx, pattern_ctx, bindings)
    }
}

impl Matches for Mul {
    fn matches(&self, pattern: &Self, ctx: &Pil, pattern_ctx: &Pil, bindings: HashMap<IndexedReferenceKey, Expression>) -> (bool, HashMap<IndexedReferenceKey, Expression>) {
        let (left_match, bindings) = self.values[0].matches(&pattern.values[0], ctx, pattern_ctx, bindings);
        if !left_match {
            let (left_match, bindings) = self.values[0].matches(&pattern.values[1], ctx, pattern_ctx, bindings);
            if !left_match {
                return (false, bindings);
            }
            self.values[1].matches(&pattern.values[0], ctx, pattern_ctx, bindings)
        } else {
            self.values[1].matches(&pattern.values[1], ctx, pattern_ctx, bindings)
        }
    }
}

impl Matches for Neg {
    fn matches(&self, pattern: &Self, ctx: &Pil, pattern_ctx: &Pil, bindings: HashMap<IndexedReferenceKey, Expression>) -> (bool, HashMap<IndexedReferenceKey, Expression>) {
        self.values[0].matches(&pattern.values[0], ctx, pattern_ctx, bindings)
    }
}

impl Visitor for PatternDetector {
    type Error = String;

    fn visit_polynomial_identity(&mut self, i: &PolIdentity, ctx: &Pil, _: usize) -> Result<Self::Error> {
        let e = ctx.get_expression(&i.e);

        if self.matches(e) {
            self.occurrences.push(e.clone());
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn detect_pattern_in_binary() {
        let pil_str = std::fs::read_to_string("binary.pil.json").unwrap();
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();

        println!("occurrences\n{}", &PatternDetector::detect(&pil));
    }
}
