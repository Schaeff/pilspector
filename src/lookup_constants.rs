use std::collections::BTreeMap;

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
    constants: BTreeMap<String, SMTStatement>,
    /// Specializations for full lookups, i.e. those cannot be combined and only applied
    /// if the constants on the right hand side of a lookup exactly match the key in this map.
    /// The expression is the body of an SMT function of the form
    /// (define-fun <lookup name> ((e1 Int) (e2 Int) ... (en Int)) Bool ...)
    /// that return true if and only if the expressions (e1, e2, ..., en) are in the lookup.
    shortcuts: BTreeMap<Vec<String>, (SMTFunction, SMTExpr)>,
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
    pub fn known_lookup_constant(&self, lookup: &ShiftedPolynomial) -> Option<String> {
        self.constants
            .iter()
            .find(|(name, _)| *lookup == Polynomial::basic(name).with_next(false))
            .map(|(name, _)| name.clone())
    }

    pub fn known_lookup_constant_escaped(&self, lookup: &ShiftedPolynomial) -> Option<String> {
        self.known_lookup_constant(lookup)
            .map(|name| escape_identifier(&name))
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
                                    self.known_lookup_constant_escaped(constant).unwrap(),
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
        self.constants
            .iter()
            .map(|(_name, def)| def.clone())
            .chain(
                self.shortcuts
                    .iter()
                    .map(|(_name, (fun, body))| define_fun(fun.clone(), body.clone())),
            )
            .collect()
    }
}

fn known_constants() -> BTreeMap<String, SMTStatement> {
    let mut result = BTreeMap::new();
    let r = SMTVariable::new("r".to_string(), SMTSort::Int);
    let v = SMTVariable::new("v".to_string(), SMTSort::Int);
    assert_eq!(
        constant_lookup_function(String::new()).args,
        vec![r.clone(), v.clone()]
    );
    result.insert(
        "Global.BYTE2".to_string(),
        define_fun(
            constant_lookup_function("Global_BYTE2".to_string()),
            and_vec(vec![
                eq(r.clone(), v.clone()), // strictly, r % 2**16 = v - this is important if this is used together with another constant in the same lookup
                ge(v.clone(), 0),
                le(v.clone(), u16::MAX as u64),
            ]),
        ),
    );
    result.insert(
        "Global.BYTE".to_string(),
        define_fun(
            constant_lookup_function("Global_BYTE".to_string()),
            and_vec(vec![
                eq(r.clone(), v.clone()), // strictly, r % 2**8 = v - this is important if this is used together with another constant in the same lookup
                ge(v.clone(), 0),
                le(v.clone(), u8::MAX as u64),
            ]),
        ),
    );
    result.insert(
        "Arith.SEL_BYTE2_BIT19".to_string(),
        define_fun(
            constant_lookup_function("Arith_SEL_BYTE2_BIT19".to_string()),
            ite(
                le(r.clone(), u16::MAX as u64),
                eq(v.clone(), 0),
                eq(v.clone(), 1),
            ),
        ),
    );
    result.insert(
        "Arith.BYTE2_BIT19".to_string(),
        define_fun(
            constant_lookup_function("Arith_BYTE2_BIT19".to_string()),
            // definition is: v == r % (2**16 + 2**19)
            // TODO This is not modeled below.
            and_vec(vec![
                eq(r.clone(), v.clone()),
                ge(v.clone(), 0),
                le(v.clone(), ((1 << 16) + (1 << 19)) - 1),
            ]),
        ),
    );
    // All the GL_SIGNED constants are built in the same way, with parameters
    // from, to, steps:
    // starts at "start", stays at a value for "steps" steps, then is incrementd by 1
    // if it reaches "end", is reset to "start" (only after the steps, i.e. "end" is
    // included in the range)
    // formally:
    // (r, v) => v == start + floor(r / steps) % (end + 1 - start)
    fn range_constant(start: i64, end: i64, step: i64) -> SMTExpr {
        let r = SMTVariable::new("r".to_string(), SMTSort::Int);
        let v = SMTVariable::new("v".to_string(), SMTSort::Int);
        let k = SMTVariable::new("k".to_string(), SMTSort::Int);
        assert_eq!(
            constant_lookup_function(String::new()).args,
            vec![r.clone(), v.clone()]
        );
        assert!(end >= start);
        let span = (end + 1 - start) as u64;
        if step == 1 {
            // v == start + r % span
            // v >= start && v <= end && exists k: v == start + r + k * span
            and_vec(vec![
                ge(v.clone(), signed_to_smt(start)),
                le(v.clone(), signed_to_smt(end)),
                exists(
                    vec![k.clone()],
                    eq(v, add(signed_to_smt(start), add(r, mul(k, span)))),
                ),
            ])
        } else {
            // v == start + floor(r / step) % span
            // v >= start && v <= end && exists k: v == start + floor(r / step) + k * span
            unimplemented!()
        }
    }
    result.insert(
        "Arith.GL_SIGNED_4BITS_C0".to_string(),
        define_fun(
            constant_lookup_function("Arith_GL_SIGNED_4BITS_C0".to_string()),
            range_constant(-16, 16, 1),
        ),
    );
    result.insert(
        "Arith.GL_SIGNED_4BITS_C1".to_string(),
        define_fun(
            constant_lookup_function("Arith_GL_SIGNED_4BITS_C1".to_string()),
            range_constant(-16, 16, 1), // TODO WRONG! Tis should be: 33
        ),
    );
    result.insert(
        "Arith.GL_SIGNED_4BITS_C2".to_string(),
        define_fun(
            constant_lookup_function("Arith_GL_SIGNED_4BITS_C2".to_string()),
            range_constant(-16, 16, 1), // TODO WRONG! Tis should be: 33 * 33
        ),
    );
    result.insert(
        "Arith.GL_SIGNED_18BITS".to_string(),
        define_fun(
            constant_lookup_function("Arith_GL_SIGNED_18BITS".to_string()),
            range_constant(-(1 << 18), 1 << 18, 1),
        ),
    );

    result.insert(
        "Binary.P_LAST".to_string(),
        define_fun(
            constant_lookup_function("Binary_P_LAST".to_string()),
            eq(
                v.clone(),
                modulo(div(r.clone(), 131072 /* 256 * 256 * 2 */), 2),
            ),
        ),
    );

    result.insert(
        "Binary.P_OPCODE".to_string(),
        define_fun(
            constant_lookup_function("Binary_P_OPCODE".to_string()),
            eq(v.clone(), div(r.clone(), 262144 /* 256 * 256 * 2 * 2*/)),
        ),
    );

    result.insert(
        "Binary.P_A".to_string(),
        define_fun(
            constant_lookup_function("Binary_P_A".to_string()),
            eq(v.clone(), modulo(div(r.clone(), 256), 256)),
        ),
    );

    result.insert(
        "Binary.P_B".to_string(),
        define_fun(
            constant_lookup_function("Binary_P_B".to_string()),
            eq(v.clone(), modulo(r.clone(), 256)),
        ),
    );

    // TODO
    result.insert(
        "Binary.P_C".to_string(),
        define_fun(
            constant_lookup_function("Binary_P_C".to_string()),
            literal_true(),
        ),
    );

    result.insert(
        "Binary.P_CIN".to_string(),
        define_fun(
            constant_lookup_function("Binary_P_CIN".to_string()),
            eq(v.clone(), modulo(div(r.clone(), 65536), 2))
        ),
    );

    // TODO
    result.insert(
        "Binary.P_COUT".to_string(),
        define_fun(
            constant_lookup_function("Binary_P_COUT".to_string()),
            literal_true(),
        ),
    );

    // TODO
    result.insert(
        "Binary.P_USE_CARRY".to_string(),
        define_fun(
            constant_lookup_function("Binary_P_USE_CARRY".to_string()),
            literal_true(),
        ),
    );

    result
}

fn known_shortcut_lookups() -> BTreeMap<Vec<String>, (SMTFunction, SMTExpr)> {
    let mut result = BTreeMap::new();
    let a = SMTVariable::new("a".to_string(), SMTSort::Int);
    let b = SMTVariable::new("b".to_string(), SMTSort::Int);
    let c = SMTVariable::new("c".to_string(), SMTSort::Int);
    result.insert(
        vec!["Global.BYTE2".to_string()],
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
        vec!["Global.BYTE".to_string()],
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
        vec![
            "Arith.SEL_BYTE2_BIT19".to_string(),
            "Arith.BYTE2_BIT19".to_string(),
        ],
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
        vec!["Arith.GL_SIGNED_18BITS".to_string()],
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
            "Arith.GL_SIGNED_4BITS_C0".to_string(),
            "Arith.GL_SIGNED_4BITS_C1".to_string(),
            "Arith.GL_SIGNED_4BITS_C2".to_string(),
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
