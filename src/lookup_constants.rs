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
    functions: Vec<SMTStatement>,
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
        [
            self.functions.clone(),
            self.constants
                .values()
                .cloned()
                .chain(
                    self.shortcuts
                        .iter()
                        .map(|(_name, (fun, body))| define_fun(fun.clone(), body.clone())),
                )
                .collect(),
        ]
        .concat()
    }
}

fn add_constant_function(result: &mut Vec<SMTStatement>, name: &str, body: SMTExpr) {
    let poly = Polynomial::basic(name.to_string());
    add_constant_function_poly(result, poly, body);
}

fn add_aux_function(result: &mut Vec<SMTStatement>, fun: SMTFunction, body: SMTExpr) {
    result.push(define_fun(fun, body));
}

fn add_aux_function_decl(result: &mut Vec<SMTStatement>, fun: SMTFunction) {
    result.push(declare_fun(
        SMTVariable::new(fun.name, fun.sort),
        fun.args.into_iter().map(|var| var.sort).collect(),
    ));
}

fn add_constant_function_poly(result: &mut Vec<SMTStatement>, poly: Polynomial, body: SMTExpr) {
    let f_name = format!("{}_function", escape_identifier(&poly.to_string()));
    result.push(define_fun(constant_lookup_function(f_name), body));
}

fn add_constant(result: &mut BTreeMap<Polynomial, SMTStatement>, name: &str, body: SMTExpr) {
    let poly = Polynomial::basic(name.to_string());
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

fn known_functions() -> Vec<SMTStatement> {
    let mut result = Vec::new();

    let r = SMTVariable::new("r".to_string(), SMTSort::Int);
    let a = SMTVariable::new("a".to_string(), SMTSort::Int);
    let b = SMTVariable::new("b".to_string(), SMTSort::Int);
    let c = SMTVariable::new("c".to_string(), SMTSort::Int);
    let d = SMTVariable::new("d".to_string(), SMTSort::Int);

    // BINARY.PIL ////////////////////

    // TODO fix
    add_constant_function(&mut result, "Binary.P_CIN", 0.into());

    add_constant_function(
        &mut result,
        "Binary.P_OPCODE",
        div(r.clone(), 262144 /* 256 * 256 * 2 * 2*/),
    );
    add_constant_function(&mut result, "Binary.P_B", modulo(r.clone(), 256));
    add_constant_function(&mut result, "Binary.P_A", modulo(div(r.clone(), 256), 256));
    add_constant_function(
        &mut result,
        "Binary.P_LAST",
        modulo(div(r.clone(), 131072 /* 256 * 256 * 2 */), 2),
    );
    // P.C

    // Declare the applications we need as dependency
    let p_a_appl = constant_lookup_function_appl("Binary.P_A".to_string(), vec![r.clone().into()]);
    let p_b_appl = constant_lookup_function_appl("Binary.P_B".to_string(), vec![r.clone().into()]);
    let p_cin_appl =
        constant_lookup_function_appl("Binary.P_CIN".to_string(), vec![r.clone().into()]);
    let p_opcode_appl =
        constant_lookup_function_appl("Binary.P_OPCODE".to_string(), vec![r.clone().into()]);
    let p_last_appl = constant_lookup_function_appl("Binary.P_LAST".to_string(), vec![r.clone().into()]);

    // Declare the variables that will be aliased to the applications
    let p_a = literal("a".to_string(), SMTSort::Int);
    let p_b = literal("b".to_string(), SMTSort::Int);
    let p_cin = literal("cin".to_string(), SMTSort::Int);
    let p_last = literal("last".to_string(), SMTSort::Int);
    let p_op = literal("op".to_string(), SMTSort::Int);

    // Build aux functions for each opcode for each {P_C, P_C_OUT, P_C_USECARRY}.
    let add_fun_c = SMTFunction::new(
        "AUX_ADD_C".to_string(),
        SMTSort::Int,
        vec![a.clone(), b.clone()],
    );
    add_aux_function(&mut result, add_fun_c, add(a.clone(), b.clone()));

    let sub_fun_c = SMTFunction::new(
        "AUX_SUB_C".to_string(),
        SMTSort::Int,
        vec![a.clone(), b.clone(), c.clone()],
    );
    add_aux_function(
        &mut result,
        sub_fun_c.clone(),
        ite(
            ge(sub(a.clone(), c.clone()), b.clone()),
            sub(a.clone(), sub(c.clone(), b.clone())),
            sub(255, add(b.clone(), sub(a.clone(), add(c.clone(), 1)))),
        ),
    );

    let lt_fun_c = SMTFunction::new(
        "AUX_LT_C".to_string(),
        SMTSort::Int,
        vec![a.clone(), b.clone(), c.clone(), d.clone()],
    );
    add_aux_function(
        &mut result,
        lt_fun_c.clone(),
        ite(
            lt(a.clone(), b.clone()),
            d.clone(),
            ite(
                eq(a.clone(), b.clone()),
                ite(eq(d.clone(), 1), c.clone(), 0),
                0,
            ),
        ),
    );

    let slt_fun_c = SMTFunction::new(
        "AUX_SLT_C".to_string(),
        SMTSort::Int,
        vec![a.clone(), b.clone(), c.clone(), d.clone()],
    );
    add_aux_function_decl(&mut result, slt_fun_c.clone());

    let eq_fun_c = SMTFunction::new(
        "AUX_EQ_C".to_string(),
        SMTSort::Int,
        vec![a.clone(), b.clone(), c, d],
    );
    add_aux_function_decl(&mut result, eq_fun_c.clone());

    let and_fun_c = SMTFunction::new(
        "AUX_AND_C".to_string(),
        SMTSort::Int,
        vec![a.clone(), b.clone()],
    );
    add_aux_function_decl(&mut result, and_fun_c.clone());

    let or_fun_c = SMTFunction::new(
        "AUX_OR_C".to_string(),
        SMTSort::Int,
        vec![a.clone(), b.clone()],
    );
    add_aux_function_decl(&mut result, or_fun_c.clone());

    let xor_fun_c = SMTFunction::new("AUX_XOR_C".to_string(), SMTSort::Int, vec![a, b]);
    add_aux_function_decl(&mut result, xor_fun_c.clone());

    // Build the opcodes
    let op_0 = modulo(add(p_cin.clone(), add(p_a.clone(), p_b.clone())), 256);
    let op_1 = uf(sub_fun_c, vec![p_a.clone(), p_b.clone(), p_cin.clone()]);
    let op_2 = uf(
        lt_fun_c,
        vec![p_a.clone(), p_b.clone(), p_cin.clone(), p_last.clone()],
    );
    let op_3 = uf(
        slt_fun_c,
        vec![p_a.clone(), p_b.clone(), p_cin.clone(), p_last.clone()],
    );
    let op_4 = uf(eq_fun_c, vec![p_a.clone(), p_b.clone(), p_cin, p_last]);
    let op_5 = uf(and_fun_c, vec![p_a.clone(), p_b.clone()]);
    let op_6 = uf(or_fun_c, vec![p_a.clone(), p_b.clone()]);
    let op_7 = uf(xor_fun_c, vec![p_a, p_b]);

    let p_c = ite(
        eq(p_op.clone(), 0),
        op_0,
        ite(
            eq(p_op.clone(), 1),
            op_1,
            ite(
                eq(p_op.clone(), 2),
                op_2,
                ite(
                    eq(p_op.clone(), 3),
                    op_3,
                    ite(
                        eq(p_op.clone(), 4),
                        op_4,
                        ite(
                            eq(p_op.clone(), 5),
                            op_5,
                            ite(eq(p_op.clone(), 6), op_6, ite(eq(p_op, 7), op_7, 0)),
                        ),
                    ),
                ),
            ),
        ),
    );
    let let_p_c = let_smt(
        vec![
            ("a".to_string(), p_a_appl),
            ("b".to_string(), p_b_appl),
            ("cin".to_string(), p_cin_appl),
            ("op".to_string(), p_opcode_appl),
            ("last".to_string(), p_last_appl),
        ],
        p_c,
    );
    add_constant_function(&mut result, "Binary.P_C", let_p_c);

    // END BINARY.PIL ////////////////////

    // This is the fixed version of the bug reported in January.
    add_constant_function(&mut result, 
        "MemAlign.BYTE_C4096", modulo(div(r.clone(), 4096), 256)
    );

    add_constant_function(&mut result, 
        "MemAlign.WR8", ge(modulo(r.clone(), 4096), 3072)
    );

    add_constant_function(&mut result, 
        "MemAlign.OFFSET", modulo(div(r.clone(), 32), 32)
    );

    let offset_appl = constant_lookup_function_appl("MemAlign.OFFSET".to_string(), vec![r.clone().into()]);
    let wr8_appl = constant_lookup_function_appl("MemAlign.WR8".to_string(), vec![r.clone().into()]);
    add_constant_function(&mut result,
        "MemAlign.V_BYTE", modulo(add(31, sub(add(offset_appl.clone(), wr8_appl.clone()), modulo(r.clone(), 32))), 32)
    );
    
    let wr8 = SMTVariable::new("wr8".to_string(), SMTSort::Int);
    let offset = SMTVariable::new("offset".to_string(), SMTSort::Int);
    let step = SMTVariable::new("step".to_string(), SMTSort::Int);
    add_constant_function(&mut result,
        "MemAlign.SELM1", let_smt(vec![
            ("wr8".to_string(), wr8_appl),
            ("offset".to_string(), offset_appl),
            ("step".to_string(), modulo(r.clone(), 32))
        ],
            ite(
                ite(
                    eq(wr8, 1),
                    eq(step.clone(), offset.clone()),
                    gt(offset, step)
                ),
                1,
                0
            )
    ));

    add_constant_function(&mut result,
        "MemAlign.P256", ite(eq(r.clone(), 0), 1,
                            ite(eq(r.clone(), 1), 256,
                                ite(eq(r.clone(), 2), 65536,
                                    ite(eq(r.clone(), 3), 16777216, 0)
                                )
                            )
                        )        
    );
    
    let vbyte_appl = constant_lookup_function_appl("MemAlign.V_BYTE".to_string(), vec![r.clone().into()]);
    let vbyte = SMTVariable::new("vbyte".to_string(), SMTSort::Int);
    for idx in 0..8 {
        add_constant_function_poly(&mut result,
            Polynomial::array_element("MemAlign.FACTORV".to_string(), idx), let_smt(vec![
                ("vbyte".to_string(), vbyte_appl.clone())
            ],
            ite(
                                    eq(div(vbyte.clone(), 4), idx as u64),
                                    constant_lookup_function_appl("MemAlign.P256".to_string(), vec![modulo(vbyte.clone(), 4)]),
                                0)
            )
        );
    }

    result
}

fn known_constants() -> BTreeMap<Polynomial, SMTStatement> {
    let mut result = BTreeMap::new();
    let r = SMTVariable::new("r".to_string(), SMTSort::Int);
    let v = SMTVariable::new("v".to_string(), SMTSort::Int);
    let b = SMTVariable::new("b".to_string(), SMTSort::Int);
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
    // starts at "start", stays at a value for "steps" steps, then is incremented by 1
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
            constant_lookup_function_appl("Binary.P_LAST".to_string(), vec![r.clone().into()]),
        ),
    );

    add_constant(
        &mut result,
        "Binary.P_OPCODE",
        eq(
            v.clone(),
            constant_lookup_function_appl("Binary.P_OPCODE".to_string(), vec![r.clone().into()]),
        ),
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

    add_constant(
        &mut result,
        "Binary.P_B",
        eq(
            v.clone(),
            constant_lookup_function_appl("Binary.P_B".to_string(), vec![r.clone().into()]),
        ),
    );

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

    for i in 0..8 {
        add_constant_poly(
            &mut result,
            Polynomial::array_element("MemAlign.FACTOR", i),
            eq(v.clone(),
                ite(
                    lt(
                        modulo(
                            sub((i*4) as u64, r.clone()),
                            32
                        ), 4
                    ),
                    constant_lookup_function_appl("MemAlign.P256".to_string(), vec![modulo(r.clone(), 4)]),
                    0
                )
            )
        );
    };
    add_constant(&mut result,
        "MemAlign.WR256",
        let_smt(
            vec![("b".to_string(), modulo(r.clone(), 4096))],
            ite(and_vec(vec![ge(r.clone(), 2048), lt(r.clone(), 3072)]), 1, 0)
        )
    );
    add_constant(&mut result,
        "MemAlign.WR8",
        eq(
            v.clone(),
            ite(constant_lookup_function_appl("MemAlign.WR8".to_string(), vec![r.clone().into()]), 1, 0)
        )
    );

    add_constant(
        &mut result,
        "MemAlign.BYTE_C4096",
        eq(
            v.clone(),
            constant_lookup_function_appl("MemAlign.BYTE_C4096".to_string(), vec![r.clone().into()]),
        ),
    );

    add_constant(&mut result, "MemAlign.OFFSET",
        eq(v.clone(),
            constant_lookup_function_appl(
                "MemAlign.OFFSET".to_string(),
                vec![r.clone().into()]
            )
        )
    );

    add_constant(&mut result, "MemAlign.SELM1",
        eq(v.clone(),
            constant_lookup_function_appl(
                "MemAlign.SELM1".to_string(),
                vec![r.clone().into()]
            )
        )
    );

    for i in 0..8 {
        let factorv_idx = Polynomial::array_element("MemAlign.FACTORV", i);
        add_constant_poly(
            &mut result,
            factorv_idx.clone(),
            eq(v.clone(), constant_lookup_function_appl(factorv_idx.clone().to_string(), vec![r.clone().into()]))
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
        vec![Polynomial::basic("Global.BYTE2".to_string())],
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
        vec![Polynomial::basic("Global.BYTE".to_string())],
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
            Polynomial::basic("Arith.SEL_BYTE2_BIT19".to_string()),
            Polynomial::basic("Arith.BYTE2_BIT19".to_string()),
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
        vec![Polynomial::basic("Arith.GL_SIGNED_18BITS".to_string())],
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
            Polynomial::basic("Arith.GL_SIGNED_4BITS_C0".to_string()),
            Polynomial::basic("Arith.GL_SIGNED_4BITS_C1".to_string()),
            Polynomial::basic("Arith.GL_SIGNED_4BITS_C2".to_string()),
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
