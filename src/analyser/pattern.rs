use std::collections::HashMap;

use crate::{
    ast::{
        Add, Cm, Const, Exp, Expression, ExpressionWrapper, Mul, Neg, Pil, PolIdentity,
        ShiftedPolynomial, Sub, ToPolynomial,
    },
    displayer::PilDisplayer,
    folder::Folder,
    visitor::Visitor,
};

pub struct PatternDetector {
    pil: Pil,
    pattern_pil: Pil,
    pattern: Expression,
    occurrences: Vec<Expression>,
}

impl PatternDetector {
    pub fn detect(pil: &Pil, pattern_pil: &Pil) -> Vec<String> {
        assert_eq!(pattern_pil.pol_identities.len(), 1, "pattern must have a single polynomial identity");
        let expression = &pattern_pil.expressions[pattern_pil.pol_identities[0].e.0];

        let mut detector = PatternDetector {
            pattern: expression.clone(),
            occurrences: vec![],
            pil: pil.clone(),
            pattern_pil: pattern_pil.clone(),
        };
        detector.visit_pil(pil).unwrap();

        detector
            .occurrences
            .iter()
            .map(|e| {
                let mut displayer = PilDisplayer::default();
                displayer.visit_expression(e, pil).unwrap();
                String::from_utf8(displayer.f).unwrap()
            })
            .collect::<Vec<_>>()
    }

    fn matches(&self, e: &Expression) -> bool {
        e.matches(
            &self.pattern,
            &self.pil,
            &self.pattern_pil,
            HashMap::default(),
        )
        .0
    }
}

trait Matches {
    fn matches(
        &self,
        pattern: &Self,
        ctx: &Pil,
        pattern_ctx: &Pil,
        bindings: HashMap<ShiftedPolynomial, Expression>,
    ) -> (bool, HashMap<ShiftedPolynomial, Expression>);
}

impl Matches for Expression {
    fn matches(
        &self,
        pattern: &Expression,
        ctx: &Pil,
        pattern_ctx: &Pil,
        mut bindings: HashMap<ShiftedPolynomial, Expression>,
    ) -> (bool, HashMap<ShiftedPolynomial, Expression>) {
        // println!("try match {} to {}", self.to_string(ctx), pattern.to_string(pattern_ctx));
        // println!("{}", bindings.iter().map(|(key, value)| format!("{} -> {}", key.to_string(), value.to_string(ctx))).collect::<Vec<_>>().join(", "));

        match (self, pattern) {
            (e, Expression::Cm(cm)) => {
                let pol = cm.inner.to_polynomial(pattern_ctx);
                let (res, to_insert) = match bindings.get(&pol) {
                    Some(bound_e) => (e == bound_e, vec![]),
                    None => {
                        // if this expression is already in the map, stop
                        if bindings.values().any(|exp| exp == e) {
                            // println!("{} was already bound", e.to_string(ctx));
                            return (false, bindings);
                        }

                        // println!("{} is not bound, try to bind it to {}", self.to_string(ctx), pattern.to_string(pattern_ctx));

                        // if this symbolic variable isn't assigned, we only assign is if its other `next` can also be assigned
                        let other_e = if pol.next {
                            RowShifter::previous(e.clone(), ctx)
                        } else {
                            RowShifter::next(e.clone(), ctx)
                        };

                        match other_e {
                            Ok(other_e) => (
                                true,
                                vec![
                                    (
                                        ShiftedPolynomial {
                                            next: !pol.next,
                                            ..pol.clone()
                                        },
                                        other_e,
                                    ),
                                    (pol, e.clone()),
                                ],
                            ),
                            Err(..) => (true, vec![]),
                        }
                    }
                };

                bindings.extend(to_insert);
                (res, bindings)
            }
            (Expression::Add(left), Expression::Add(right)) => {
                left.matches(right, ctx, pattern_ctx, bindings)
            }
            (Expression::Sub(left), Expression::Sub(right)) => {
                left.matches(right, ctx, pattern_ctx, bindings)
            }
            (Expression::Neg(left), Expression::Neg(right)) => {
                left.matches(right, ctx, pattern_ctx, bindings)
            }
            (Expression::Mul(left), Expression::Mul(right)) => {
                left.matches(right, ctx, pattern_ctx, bindings)
            }
            (Expression::Number(_), Expression::Number(_)) => (true, bindings),
            (Expression::Const(_), Expression::Const(_)) => (true, bindings),
            (_e, _p) => {
                // println!("failed to match {} to {}", e.to_string(ctx), p.to_string(pattern_ctx));
                (false, bindings)
            }
        }
    }
}

impl<E: Matches> Matches for ExpressionWrapper<E> {
    fn matches(
        &self,
        pattern: &Self,
        ctx: &Pil,
        pattern_ctx: &Pil,
        bindings: HashMap<ShiftedPolynomial, Expression>,
    ) -> (bool, HashMap<ShiftedPolynomial, Expression>) {
        self.inner
            .matches(&pattern.inner, ctx, pattern_ctx, bindings)
    }
}

impl Matches for Add {
    fn matches(
        &self,
        pattern: &Self,
        ctx: &Pil,
        pattern_ctx: &Pil,
        bindings: HashMap<ShiftedPolynomial, Expression>,
    ) -> (bool, HashMap<ShiftedPolynomial, Expression>) {
        let (left_match, bindings) =
            self.values[0].matches(&pattern.values[0], ctx, pattern_ctx, bindings);
        if !left_match {
            let (left_match, bindings) =
                self.values[0].matches(&pattern.values[1], ctx, pattern_ctx, bindings);
            if !left_match {
                return (false, bindings);
            }
            self.values[1].matches(&pattern.values[0], ctx, pattern_ctx, bindings)
        } else {
            self.values[1].matches(&pattern.values[1], ctx, pattern_ctx, bindings)
        }
    }
}

impl Matches for Sub {
    fn matches(
        &self,
        pattern: &Self,
        ctx: &Pil,
        pattern_ctx: &Pil,
        bindings: HashMap<ShiftedPolynomial, Expression>,
    ) -> (bool, HashMap<ShiftedPolynomial, Expression>) {
        let (left_match, bindings) =
            self.values[0].matches(&pattern.values[0], ctx, pattern_ctx, bindings);
        if !left_match {
            return (false, bindings);
        }
        self.values[1].matches(&pattern.values[1], ctx, pattern_ctx, bindings)
    }
}

impl Matches for Mul {
    fn matches(
        &self,
        pattern: &Self,
        ctx: &Pil,
        pattern_ctx: &Pil,
        bindings: HashMap<ShiftedPolynomial, Expression>,
    ) -> (bool, HashMap<ShiftedPolynomial, Expression>) {
        let (left_match, bindings) =
            self.values[0].matches(&pattern.values[0], ctx, pattern_ctx, bindings);
        if !left_match {
            let (left_match, bindings) =
                self.values[0].matches(&pattern.values[1], ctx, pattern_ctx, bindings);
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
    fn matches(
        &self,
        pattern: &Self,
        ctx: &Pil,
        pattern_ctx: &Pil,
        bindings: HashMap<ShiftedPolynomial, Expression>,
    ) -> (bool, HashMap<ShiftedPolynomial, Expression>) {
        self.values[0].matches(&pattern.values[0], ctx, pattern_ctx, bindings)
    }
}

impl Visitor for PatternDetector {
    type Error = String;

    fn visit_polynomial_identity(
        &mut self,
        i: &PolIdentity,
        ctx: &Pil,
        _: usize,
    ) -> crate::visitor::Result<Self::Error> {
        let e = &ctx.expressions[i.e.0];

        if self.matches(e) {
            self.occurrences.push(e.clone());
        }

        Ok(())
    }
}

// a folder which tries to shift an expression forward or backwards
// forward: a -> a' , a' -> error
// backwards: a' -> a, a -> error
struct RowShifter {
    forward: bool,
}

impl RowShifter {
    fn next(e: Expression, ctx: &Pil) -> Result<Expression, ()> {
        RowShifter { forward: true }.fold_expression(e, ctx)
    }

    fn previous(e: Expression, ctx: &Pil) -> Result<Expression, ()> {
        RowShifter { forward: false }.fold_expression(e, ctx)
    }
}

impl Folder for RowShifter {
    type Error = ();

    fn fold_cm(&mut self, cm: Cm, _ctx: &Pil) -> Result<Cm, Self::Error> {
        if self.forward == cm.next {
            Err(())
        } else {
            Ok(Cm {
                next: self.forward,
                ..cm
            })
        }
    }

    fn fold_const(&mut self, c: Const, _ctx: &Pil) -> Result<Const, Self::Error> {
        if self.forward == c.next {
            Err(())
        } else {
            Ok(Const {
                next: self.forward,
                ..c
            })
        }
    }

    fn fold_exp(&mut self, exp: Exp, _ctx: &Pil) -> Result<Exp, Self::Error> {
        if self.forward == exp.next {
            Err(())
        } else {
            Ok(Exp {
                next: self.forward,
                ..exp
            })
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{pilcom, pilcom_from_str};

    use super::*;

    #[test]
    fn detect_pattern_in_binary() {
        let pil: Pil = serde_json::from_str(&pilcom("pil/zkevm/binary.pil").unwrap()).unwrap();

        let pattern = r#"
        namespace Pattern(%N);
            pol commit cIn, RESET, cOut;
            cIn' * ( 1 - RESET' ) = cOut * ( 1 - RESET' );
    "#;

        let pattern: Pil = serde_json::from_str(&pilcom_from_str(pattern).unwrap()).unwrap();

        assert_eq!(PatternDetector::detect(&pil, &pattern).len(), 1);
    }
}
