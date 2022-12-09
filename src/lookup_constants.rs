use std::collections::BTreeMap;

use crate::smt::*;

pub fn constant_lookup_function(name: String) -> SMTFunction {
    let r = SMTVariable::new("r".to_string(), SMTSort::Int);
    let v = SMTVariable::new("v".to_string(), SMTSort::Int);
    SMTFunction::new(name, SMTSort::Bool, vec![r, v])
}

pub fn known_constants() -> BTreeMap<String, SMTStatement> {
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
            eq(v, modulo(div(r, 256), 256)),
        ),
    );

    // TODO
    result.insert(
        "Binary.P_B".to_string(),
        define_fun(
            constant_lookup_function("Binary_P_B".to_string()),
            literal_true(),
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

    // TODO
    result.insert(
        "Binary.P_CIN".to_string(),
        define_fun(
            constant_lookup_function("Binary_P_CIN".to_string()),
            literal_true(),
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
