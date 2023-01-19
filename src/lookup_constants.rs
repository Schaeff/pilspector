use std::collections::BTreeMap;

use crate::ast::*;
use crate::smt::*;
use crate::smt_encoder::escape_identifier;

fn constant_lookup_predicate(name: String) -> SMTFunction {
    let r = SMTVariable::new("r".to_string(), SMTSort::Int);
    let v = SMTVariable::new("v".to_string(), SMTSort::Int);
    SMTFunction::new(name, SMTSort::Bool, vec![r, v])
}

fn constant_lookup_function(name: String) -> SMTFunction {
    let r = SMTVariable::new("r".to_string(), SMTSort::Int);
    SMTFunction::new(name, SMTSort::Int, vec![r])
}

fn constant_lookup_function_appl(name: String, args: Vec<SMTExpr>) -> SMTExpr {
    uf(
        constant_lookup_function(format!("{}_function", escape_identifier(name.as_str()))),
        args,
    )
}

fn constant_function_predicate(poly: Polynomial) -> String {
    format!("const_{}", escape_identifier(&poly.to_string()))
}

#[derive(Debug, Clone)]
pub struct LookupConstants {
    /// Definition of constants so that they can also be used in lookups and
    /// arbitrarily combined with other lookups.
    /// The statement should be SMT functions of the form
    /// (define-fun <constant name> ((row Int) (v Int)) Bool ...)
    /// that return true if and only if the constant value in row `row`
    /// is equal to `v`.
    /// The lookup (e1, e2, ..., en) in (l1, l2, ..., ln) is translated to
    /// (exists ((row Int)) (and (l1 row e1) (l2 row e2) ... (ln row e2)))
    constants: BTreeMap<Polynomial, SMTStatement>,
    /// Some constants are more easily represented by functions,
    /// especially when they are reused by other constants.
    /// For example, Binary.P_A and Binary.P_B are used in the RHS
    /// of lookups, but they are also used in Binary.P_C.
    /// For these we define functions that return the value based on
    /// the row, and define the predicate as a wrapper that uses such
    /// function and constrains the given row and value.
    functions: BTreeMap<Polynomial, SMTStatement>,
    /// Specializations for full lookups, i.e. those cannot be combined and only applied
    /// if the constants on the right hand side of a lookup exactly match the key in this map.
    /// The expression is the body of an SMT function of the form
    /// (define-fun <lookup name> ((e1 Int) (e2 Int) ... (en Int)) Bool ...)
    /// that return true if and only if the expressions (e1, e2, ..., en) are in the lookup.
    shortcuts: BTreeMap<Vec<Polynomial>, (SMTFunction, SMTExpr)>,
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
            functions: known_functions(),
            shortcuts: known_shortcut_lookups(),
        }
    }

    /// @returns true iff we know this constant. Returns false if "next" is set to true.
    pub fn is_known_constant(&self, lookup: &ShiftedPolynomial) -> bool {
        self.known_lookup_constant(lookup).is_some()
    }

    fn known_lookup_constant(&self, lookup: &ShiftedPolynomial) -> Option<Polynomial> {
        if lookup.next {
            return None;
        }

        self.constants
            .get_key_value(&lookup.pol)
            .map(|(p, _)| p.clone())
    }

    pub fn known_lookup_constant_as_predicate(
        &self,
        lookup: &ShiftedPolynomial,
    ) -> Option<SMTFunction> {
        self.known_lookup_constant(lookup)
            .map(constant_function_predicate)
            .map(constant_lookup_predicate)
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
                "; No specialized lookup found for combination {:?} - will need to use quantifiers.",
                constants
            );
            let row = SMTVariable::new("row".to_string(), SMTSort::Int);
            exists(
                vec![row.clone()],
                and_vec(
                    [
                        vec![ge(row.clone(), 0)],
                        lhs.into_iter()
                            .zip(rhs.iter())
                            .map(|(expr, constant)| {
                                uf(
                                    self.known_lookup_constant_as_predicate(constant).unwrap(),
                                    vec![row.clone().into(), expr],
                                )
                            })
                            .collect(),
                    ]
                    .concat(),
                ),
            )
        }
    }

    pub fn function_definitions(&self) -> Vec<SMTStatement> {
        self.functions
            .iter()
            .chain(self.constants.iter())
            .map(|(_name, def)| def.clone())
            .chain(
                self.shortcuts
                    .iter()
                    .map(|(_name, (fun, body))| define_fun(fun.clone(), body.clone())),
            )
            .collect()
    }
}

fn add_constant_function(
    result: &mut BTreeMap<Polynomial, SMTStatement>,
    name: &str,
    body: SMTExpr,
) {
    let poly = Polynomial::basic(&name.to_string());
    add_constant_function_poly(result, poly, body);
}

fn add_constant_function_poly(
    result: &mut BTreeMap<Polynomial, SMTStatement>,
    poly: Polynomial,
    body: SMTExpr,
) {
    let f_name = format!("{}_function", escape_identifier(&poly.to_string()));
    result.insert(poly, define_fun(constant_lookup_function(f_name), body));
}

fn add_constant(result: &mut BTreeMap<Polynomial, SMTStatement>, name: &str, body: SMTExpr) {
    let poly = Polynomial::basic(&name.to_string());
    add_constant_poly(result, poly, body);
}

fn add_constant_poly(
    result: &mut BTreeMap<Polynomial, SMTStatement>,
    poly: Polynomial,
    body: SMTExpr,
) {
    result.insert(
        poly.clone(),
        define_fun(
            constant_lookup_predicate(constant_function_predicate(poly)),
            body,
        ),
    );
}

fn known_functions() -> BTreeMap<Polynomial, SMTStatement> {
    let mut result = BTreeMap::new();

    let r = SMTVariable::new("r".to_string(), SMTSort::Int);

    add_constant_function(&mut result, "Binary.P_A", modulo(div(r.clone(), 256), 256));

    // This is wrong, missing a mod 256 here. But was already reported in january.
    add_constant_function(&mut result, "MemAlign.BYTE_C4096", modulo(div(r.clone(), 4096), 256));

    result
}

fn known_constants() -> BTreeMap<Polynomial, SMTStatement> {
    let mut result = BTreeMap::new();
    let r = SMTVariable::new("r".to_string(), SMTSort::Int);
    let v = SMTVariable::new("v".to_string(), SMTSort::Int);
    assert_eq!(
        constant_lookup_predicate(String::new()).args,
        vec![r.clone(), v.clone()]
    );
    add_constant(
        &mut result,
        "Global.BYTE2",
        and_vec(vec![
            eq(r.clone(), v.clone()), // strictly, r % 2**16 = v - this is important if this is used together with another constant in the same lookup
            ge(v.clone(), 0),
            le(v.clone(), u16::MAX as u64),
        ]),
    );
    add_constant(
        &mut result,
        "Global.BYTE",
        eq(v.clone(), modulo(r.clone(), 256)),
    );
    add_constant(
        &mut result,
        "Global.BYTE_2A",
        eq(v.clone(), modulo(div(r.clone(), 256), 256)),
    );
    add_constant(&mut result, "Global.STEP32", eq(v.clone(), modulo(r.clone(), 32)));
    for i in 0..32 {
        add_constant_poly(
            &mut result,
            Polynomial::array_element("Global.CLK32", i),
            eq(v.clone(), ite(eq(modulo(r.clone(), 32), i as u64), 1, 0)),
        );
    }
    add_constant(
        &mut result,
        "Arith.SEL_BYTE2_BIT19",
        ite(
            le(r.clone(), u16::MAX as u64),
            eq(v.clone(), 0),
            eq(v.clone(), 1),
        ),
    );
    add_constant(
        &mut result,
        "Arith.BYTE2_BIT19",
        and_vec(vec![eq(
            v.clone(),
            modulo(r.clone(), (1 << 16) + (1 << 19)),
        )]),
    );
    // All the GL_SIGNED constants are built in the same way, with parameters
    // from, to, steps:
    // starts at "start", stays at a value for "steps" steps, then is incrementd by 1
    // if it reaches "end", is reset to "start" (only after the steps, i.e. "end" is
    // included in the range)
    // formally:
    // (r, v) => v == start + floor(r / steps) % (end + 1 - start)
    fn range_constant(start: i64, end: i64, step: u64) -> SMTExpr {
        let r = SMTVariable::new("r".to_string(), SMTSort::Int);
        let v = SMTVariable::new("v".to_string(), SMTSort::Int);
        assert_eq!(
            constant_lookup_predicate(String::new()).args,
            vec![r.clone(), v.clone()]
        );
        assert!(end >= start);
        let span = (end + 1 - start) as u64;
        if step == 1 {
            // v == start + r % span
            // v >= start && v <= end && exists k: v == start + r + k * span
            eq(v, add(signed_to_smt(start), modulo(r, span)))
        } else {
            // v == start + floor(r / step) % span
            // v >= start && v <= end && exists k: v == start + floor(r / step) + k * span
            eq(v, add(signed_to_smt(start), modulo(div(r, step), span)))
        }
    }
    add_constant(
        &mut result,
        "Arith.GL_SIGNED_4BITS_C0",
        range_constant(-16, 16, 1),
    );
    add_constant(
        &mut result,
        "Arith.GL_SIGNED_4BITS_C1",
        range_constant(-16, 16, 33),
    );
    add_constant(
        &mut result,
        "Arith.GL_SIGNED_4BITS_C2",
        range_constant(-16, 16, 33 * 33),
    );
    add_constant(
        &mut result,
        "Arith.GL_SIGNED_18BITS",
        range_constant(-(1 << 18), 1 << 18, 1),
    );

    add_constant(&mut result, "Mem.ISNOTLAST", eq(v.clone(), 1));

    add_constant(&mut result, "Mem.INCS", eq(v.clone(), add(r.clone(), 1)));

    add_constant(
        &mut result,
        "Binary.P_LAST",
        eq(
            v.clone(),
            modulo(div(r.clone(), 131072 /* 256 * 256 * 2 */), 2),
        ),
    );

    add_constant(
        &mut result,
        "Binary.P_OPCODE",
        eq(v.clone(), div(r.clone(), 262144 /* 256 * 256 * 2 * 2*/)),
    );

    add_constant(
        &mut result,
        "Byte4.SET",
        eq(v.clone(), ite(eq_zero(modulo(r.clone(), 2)), 1, 0)),
    );

    add_constant(
        &mut result,
        "Binary.P_A",
        eq(
            v.clone(),
            constant_lookup_function_appl("Binary.P_A".to_string(), vec![r.clone().into()]),
        ),
    );

    // TODO
    add_constant(&mut result, "Binary.P_B", literal_true());
    // TODO
    add_constant(&mut result, "Binary.P_C", literal_true());
    // TODO
    add_constant(&mut result, "Binary.P_CIN", literal_true());
    // TODO
    add_constant(&mut result, "Binary.P_COUT", literal_true());
    // TODO
    add_constant(&mut result, "Binary.P_USE_CARRY", literal_true());
    add_constant(
        &mut result,
        "Binary.RESET",
        eq(v.clone(), ite(eq(modulo(r.clone(), 8 * 4), 0), 1, 0)),
    );

    add_constant(&mut result, "MemAlign.OFFSET",
        eq(v.clone(),
            constant_lookup_function_appl(
                "MemAlign.OFFSET".to_string(),
                vec![r.clone().into()]
            )
        )
    );
    // TODO...
    add_constant(&mut result, "MemAlign.WR256", literal_true());
    add_constant(&mut result, "MemAlign.WR8", literal_true());
    for i in 0..8 {
        add_constant_poly(
            &mut result,
            Polynomial::array_element("MemAlign.FACTOR", i),
            literal_true(),
        );
        add_constant_poly(
            &mut result,
            Polynomial::array_element("MemAlign.FACTORV", i),
            literal_true(),
        );
    }

    result
}

fn known_shortcut_lookups() -> BTreeMap<Vec<Polynomial>, (SMTFunction, SMTExpr)> {
    let mut result = BTreeMap::new();
    let a = SMTVariable::new("a".to_string(), SMTSort::Int);
    let b = SMTVariable::new("b".to_string(), SMTSort::Int);
    let c = SMTVariable::new("c".to_string(), SMTSort::Int);
    result.insert(
        vec![Polynomial::basic(&"Global.BYTE2".to_string())],
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
        vec![Polynomial::basic(&"Global.BYTE".to_string())],
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
            Polynomial::basic(&"Arith.SEL_BYTE2_BIT19".to_string()),
            Polynomial::basic(&"Arith.BYTE2_BIT19".to_string()),
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
        vec![Polynomial::basic(&"Arith.GL_SIGNED_18BITS".to_string())],
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
            Polynomial::basic(&"Arith.GL_SIGNED_4BITS_C0".to_string()),
            Polynomial::basic(&"Arith.GL_SIGNED_4BITS_C1".to_string()),
            Polynomial::basic(&"Arith.GL_SIGNED_4BITS_C2".to_string()),
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
                le(a.clone(), 16),
                ge(b.clone(), signed_to_smt(-16)),
                le(b.clone(), 16),
                ge(c.clone(), signed_to_smt(-16)),
                le(c, 16),
            ]),
        ),
    );

    result.insert(
        vec![
            Polynomial::basic(&"Global.BYTE_2A".to_string()),
            Polynomial::basic(&"Global.BYTE".to_string()),
        ], (
        SMTFunction::new(
            "MemAlign_BYTE_CONSTRAINT".to_string(),
            SMTSort::Bool,
            vec![a.clone(), b.clone()],
        ),
        and_vec(vec![
            ge(a.clone(), 0),
            le(a.clone(), 255),
            ge(b.clone(), 0),
            le(b.clone(), 255),
        ]))
    );
    result
}
