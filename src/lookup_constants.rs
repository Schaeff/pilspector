use std::collections::BTreeMap;
use std::collections::BTreeSet;

use regex::Regex;

use crate::ast::*;
use crate::smt::*;
use crate::smt_encoder::escape_identifier;

pub fn constant_lookup_function(name: String) -> SMTFunction {
    let r = SMTVariable::new("r".to_string(), SMTSort::Int);
    let v = SMTVariable::new("v".to_string(), SMTSort::Int);
    SMTFunction::new(name, SMTSort::Bool, vec![r, v])
}

#[derive(Debug, Clone)]
pub struct LookupConstants {
    /// Definition of constant lookups that can be arbitrarily combined with other lookups.
    /// The statement should be SMT functions of the form
    /// (define-fun <constant name> ((row Int) (v Int)) Bool ...)
    /// that return true if and only if the constant value in row `row`
    /// is equal to `v`.
    /// The lookup (e1, e2, ..., en) in (l1, l2, ..., ln) is translated to
    /// (exists ((row Int)) (and (l1 row e1) (l2 row e2) ... (ln row e2)))
    constants: BTreeSet<&'static str>,
    /// Specializations for full lookups, i.e. those cannot be combined and only applied
    /// if the constants on the right hand side of a lookup exactly match the key in this map.
    /// The expression is the body of an SMT function of the form
    /// (define-fun <lookup name> ((e1 Int) (e2 Int) ... (en Int)) Bool ...)
    /// that return true if and only if the expressions (e1, e2, ..., en) are in the lookup.
    shortcuts: BTreeMap<Vec<&'static str>, (SMTFunction, SMTExpr)>,
}

impl Default for LookupConstants {
    fn default() -> Self {
        Self::new()
    }
}

impl LookupConstants {
    pub fn new() -> LookupConstants {
        LookupConstants {
            constants: known_constants(),
            shortcuts: known_shortcut_lookups(),
        }
    }
    pub fn known_lookup_constant(&self, lookup: &ShiftedPolynomial) -> Option<&'static str> {
        self.constants
            .get(escape_identifier(&lookup.to_string()).as_str())
            .copied()
    }

    pub fn encode_lookup(&self, lhs: Vec<SMTExpr>, rhs: Vec<ShiftedPolynomial>) -> SMTExpr {
        assert_eq!(lhs.len(), rhs.len());
        let constants = rhs
            .iter()
            .map(|constant| self.known_lookup_constant(constant).unwrap())
            .collect::<Vec<_>>();
        if let Some((shortcut, _)) = self.shortcuts.get(&constants) {
            uf(shortcut.clone(), lhs)
        } else {
            println!(
                "; No specialized lookup found for combination {} - will need to use quantifiers.",
                constants.join(", ")
            );
            let row = SMTVariable::new("row".to_string(), SMTSort::Int);
            exists(
                vec![row.clone()],
                and_vec(
                    lhs.into_iter()
                        .zip(rhs.iter())
                        .map(|(expr, constant)| {
                            uf(
                                constant_lookup_function(
                                    self.known_lookup_constant(constant).unwrap().to_string(),
                                ),
                                vec![row.clone().into(), expr],
                            )
                        })
                        .collect(),
                ),
            )
        }
    }

    pub fn function_definitions(&self) -> Vec<SMTStatement> {
        self.shortcuts
            .iter()
            .map(|(_name, (fun, body))| define_fun(fun.clone(), body.clone()))
            .collect()
    }
}

fn known_constants() -> BTreeSet<&'static str> {
    let re =
        Regex::new(r"\(define-fun\s+([_a-zA-Z0-9]+)\s*\(\(r Int\)\s*\(v Int\)\)\s*Bool").unwrap();
    re.captures_iter(SMT_PREAMBLE)
        .map(|cap| cap.get(1).unwrap().as_str())
        .collect()
}

fn known_shortcut_lookups() -> BTreeMap<Vec<&'static str>, (SMTFunction, SMTExpr)> {
    let mut result = BTreeMap::new();
    let a = SMTVariable::new("a".to_string(), SMTSort::Int);
    let b = SMTVariable::new("b".to_string(), SMTSort::Int);
    let c = SMTVariable::new("c".to_string(), SMTSort::Int);
    result.insert(
        vec!["Global_BYTE2"],
        (
            SMTFunction::new(
                "Global_BYTE2_isolated".to_string(),
                SMTSort::Bool,
                vec![a.clone()],
            ),
            and_vec(vec![ge(a.clone(), 0), le(a.clone(), u16::MAX as u64)]),
        ),
    );
    result.insert(
        vec!["Global_BYTE"],
        (
            SMTFunction::new(
                "Global_BYTE_isolated".to_string(),
                SMTSort::Bool,
                vec![a.clone()],
            ),
            and_vec(vec![ge(a.clone(), 0), le(a.clone(), u8::MAX as u64)]),
        ),
    );
    result.insert(
        vec!["Arith_SEL_BYTE2_BIT19", "Arith_BYTE2_BIT19"],
        (
            SMTFunction::new(
                "Arith_SEL_BYTE2_BIT19_AND_BYTE2_BIT19".to_string(),
                SMTSort::Bool,
                vec![a.clone(), b.clone()],
            ),
            // SEL_BYTE2_BIT19(r) = r < 2**16 ? 0 : 1
            // BYTE2_BIT19(r) = r % (2**19 + 2**16)
            // combined: a == 0 || a == 1 && ite(a == 0, 0 <= b < 2**16, 0 <= b < 2**16 + 2**19)
            and_vec(vec![
                ge(a.clone(), 0),
                le(a.clone(), 1),
                ge(b.clone(), 0),
                ite(
                    eq(a.clone(), 0),
                    le(b.clone(), (1 << 16) - 1),
                    le(b.clone(), (1 << 19) + (1 << 16) - 1),
                ),
            ]),
        ),
    );
    result.insert(
        vec!["Arith_GL_SIGNED_18BITS"],
        (
            SMTFunction::new(
                "Arith_GL_SIGNED_18BITS_isolated".to_string(),
                SMTSort::Bool,
                vec![a.clone()],
            ),
            and_vec(vec![
                ge(a.clone(), signed_to_smt(-(1 << 18))),
                le(a.clone(), signed_to_smt(1 << 18)),
            ]),
        ),
    );
    result.insert(
        vec![
            "Arith_GL_SIGNED_4BITS_C0",
            "Arith_GL_SIGNED_4BITS_C1",
            "Arith_GL_SIGNED_4BITS_C2",
        ],
        (
            SMTFunction::new(
                "Arith_GL_SIGNED_4BITS_C0_till_C2".to_string(),
                SMTSort::Bool,
                vec![a.clone(), b.clone(), c.clone()],
            ),
            // (r, v) => v == start + floor(r / steps) % (end + 1 - start)
            // C0: start: -16, end: 16, step: 1
            // C1: start: -16, end: 16, step: 33
            // C2: start: -16, end: 16, step: 33 * 33
            // in summary:
            // let x = a + 16, y = b + 16, z = c + 16, then:
            // 0 <= x, y, z <= 32
            // (r, x) == true <=> x == r % 33
            // (r, y) == true <=> y == floor(r / 33) % 33
            // (r, z) == true <=> z == floor(r / 33 / 33) % 33
            //
            // TODO is it just me or are x, y, z totally independent of each other?
            and_vec(vec![
                ge(a.clone(), signed_to_smt(-16)),
                le(a, 16),
                ge(b.clone(), signed_to_smt(-16)),
                le(b, 16),
                ge(c.clone(), signed_to_smt(-16)),
                le(c, 16),
            ]),
        ),
    );

    result
}
