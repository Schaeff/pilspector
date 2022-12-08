use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fmt;

use crate::ast::*;
use crate::smt::*;
use crate::visitor::*;

fn constant_lookup_function(name: String) -> SMTFunction {
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
                eq(r, v.clone()),
                ge(v.clone(), 0),
                le(v, ((1 << 16) + (1 << 19)) - 1),
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

    result
}

pub struct SmtPil {
    pil: Pil,
    /// Known constants. These can only be used in lookups.
    /// The statement should be SMT functions of the form
    /// (define-fun <constant name> ((row Int) (v Int)) Bool ...)
    /// that return true if and only if the constant value in row `row`
    /// is equal to `v`.
    constants: BTreeMap<String, SMTStatement>,
}

impl SmtPil {
    pub fn new(pil: Pil, constants: BTreeMap<String, SMTStatement>) -> Self {
        Self { pil, constants }
    }
}

enum Constraint {
    Identity(PolIdentity),
    Lookup(PlookupIdentity),
}

pub struct SmtEncoder {
    pub smt: Vec<SMTStatement>,
    funs: Vec<(SMTFunction, Constraint)>,
    constants: BTreeMap<String, SMTStatement>,
}

impl SmtEncoder {
    fn out(&mut self, statement: SMTStatement) {
        self.smt.push(statement);
    }

    fn out_vec(&mut self, statements: Vec<SMTStatement>) {
        self.smt.extend(statements);
    }
}

impl fmt::Display for SmtPil {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut encoder = SmtEncoder {
            smt: Vec::default(),
            funs: Vec::default(),
            constants: self.constants.clone(),
        };
        encoder.define_constants();
        encoder.visit_pil(&self.pil)?;

        writeln!(
            f,
            "; Uncomment the line below to enable proofs\n;(set-option :produce-proofs true)"
        )?;
        writeln!(
            f,
            "{}",
            encoder
                .smt
                .iter()
                .map(|s| s.as_smt())
                .collect::<Vec<_>>()
                .join("\n")
        )?;

        writeln!(f, "(check-sat)\n(get-model)")?;

        Ok(())
    }
}

struct VariableCollector {
    vars: BTreeSet<(IndexedReferenceKey, bool)>,
    consts: BTreeSet<(IndexedReferenceKey, bool)>,
}

impl VariableCollector {
    fn new() -> Self {
        Self {
            vars: BTreeSet::default(),
            consts: BTreeSet::default(),
        }
    }
}

impl Visitor for VariableCollector {
    type Error = ();

    fn visit_cm(&mut self, cm: &Cm, ctx: &Pil) -> Result<Self::Error> {
        let (key, _) = ctx.get_cm_reference(cm);
        self.vars.insert((key, cm.next));
        Ok(())
    }

    fn visit_exp(&mut self, exp: &Exp, ctx: &Pil) -> Result<Self::Error> {
        let (key, _) = ctx.get_exp_reference(exp);
        self.vars.insert((key, exp.next));
        Ok(())
    }

    fn visit_const(&mut self, c: &Const, ctx: &Pil) -> Result<Self::Error> {
        let (key, _) = ctx.get_const_reference(c);
        self.consts.insert((key, c.next));
        Ok(())
    }
}

fn escape_identifier(input: &str) -> String {
    input.replace(['.', '['], "_").replace(']', "")
}

// Some helpers.
impl SmtEncoder {
    fn key_to_smt_var(
        &self,
        key: &IndexedReferenceKey,
        next: bool,
        suffix: Option<String>,
    ) -> SMTVariable {
        let mut key = escape_identifier(&key.to_string());
        if next {
            key = format!("{}_next", key);
        }
        if suffix.is_some() {
            key = format!("{}_{}", key, suffix.unwrap());
        }
        SMTVariable::new(key, SMTSort::Int)
    }

    fn constr_to_smt_function(&self, i: &PolIdentity, constr_idx: usize, ctx: &Pil) -> SMTFunction {
        let mut collector = VariableCollector::new();
        let constr = &ctx.expressions[i.e.0];
        collector.visit_expression(constr, ctx).unwrap();
        let smt_vars: Vec<_> = collector
            .vars
            .iter()
            .map(|(key, next)| self.key_to_smt_var(key, *next, None))
            .collect();
        SMTFunction::new(format!("constr_{}", constr_idx), SMTSort::Bool, smt_vars)
    }

    fn define_constants(&mut self) {
        let constants = self
            .constants
            .iter()
            .map(|(_name, fun)| fun.clone())
            .collect::<Vec<_>>();
        for c in constants {
            self.out(c);
        }
    }

    fn encode_query(&self, p: &Pil, state_machine: &SMTFunction, rows: usize) -> Vec<SMTStatement> {
        let mut decls: Vec<SMTVariable> = vec![];
        let mut appls: Vec<SMTExpr> = vec![];
        let mut rows_constrs: Vec<SMTExpr> = vec![];

        (0..rows).for_each(|row| {
            let smt_row = SMTVariable::new(format!("row{}", row), SMTSort::Int);
            if row > 0 {
                let smt_prev_row = SMTVariable::new(format!("row{}", row - 1), SMTSort::Int);
                rows_constrs.push(eq(
                    smt_row.clone(),
                    add(smt_prev_row, 1)
                ));
            }
            (0..=1).for_each(|exec| {
                let mut inner_decls: Vec<SMTVariable> = vec![smt_row.clone()];
                inner_decls.extend(state_machine
                    .args
                    .iter()
                    .skip(1)
                    .map(|arg| {
                        SMTVariable::new(
                            format!("{}_row{}_exec{}", arg.name, row, exec),
                            arg.sort.clone(),
                        )
                    })
                    .collect::<Vec<_>>()
                );
                appls.push(uf(
                    state_machine.clone(),
                    inner_decls
                        .clone()
                        .into_iter()
                        .map(|decl| decl.into())
                        .collect(),
                ));
                decls.extend(inner_decls);
            })
        });

        let mut statements: Vec<SMTStatement> = decls.into_iter().map(declare_const).collect();
        statements.push(assert(and_vec(vec![rows_constrs, appls].concat())));

        // TODO add equalities between out_r1 and out_next_r0
        // TODO add equalities between in_r0_e0 and in_r0_e1
        // TODO add query on final output variables

        statements
    }

    fn encode_state_machine(&self, p: &Pil) -> (SMTFunction, SMTExpr) {
        let mut const_collector = VariableCollector::new();
        self.funs.iter().for_each(|(_, constr)| {
            if let Constraint::Identity(i) = constr {
                // The index 0 below is not used in the visitor.
                const_collector.visit_polynomial_identity(i, p, 0).unwrap();
            }
        });
        let mut smt_vars: Vec<_> = vec![SMTVariable::new("row".to_string(), SMTSort::Int)];
        smt_vars.extend(const_collector
            .consts
            .iter()
            .map(|(key, next)| self.key_to_smt_var(key, *next, None))
            .collect::<Vec<_>>()
        );

        let mut collector = VariableCollector::new();
        collector.visit_pil(p).unwrap();
        smt_vars.extend(
            collector
                .vars
                .iter()
                .map(|(key, next)| self.key_to_smt_var(key, *next, None))
                .collect::<Vec<_>>(),
        );

        let body = and_vec(
            self.funs
                .iter()
                .map(|(f, _)| uf(f.clone(), f.args.iter().map(|v| v.clone().into()).collect()))
                .collect::<Vec<_>>(),
        );

        (
            SMTFunction::new("state_machine".to_string(), SMTSort::Bool, smt_vars),
            body,
        )
    }
}

impl Visitor for SmtEncoder {
    type Error = std::fmt::Error;

    fn visit_pil(&mut self, p: &Pil) -> Result<Self::Error> {
        let ctx = p;

        for (index, identity) in p.plookup_identities.iter().enumerate() {
            self.visit_plookup_identity(identity, ctx, index)?;
        }

        for (index, identity) in p.permutation_identities.iter().enumerate() {
            self.visit_permutation_identity(identity, ctx, index)?;
        }

        for (index, identity) in p.connection_identities.iter().enumerate() {
            self.visit_connection_identity(identity, ctx, index)?;
        }

        for (index, identity) in p.pol_identities.iter().enumerate() {
            self.visit_polynomial_identity(identity, ctx, index)?;
        }

        let (state_function, body) = self.encode_state_machine(p);
        self.out(define_fun(state_function.clone(), body));

        let query = self.encode_query(p, &state_function, 3);
        self.out_vec(query);

        Ok(())
    }

    fn visit_public_cell(&mut self, _cell: &PublicCell, _ctx: &Pil) -> Result<Self::Error> {
        unimplemented!("declaration of public values is not supported")
    }

    fn visit_polynomial_identity(
        &mut self,
        i: &PolIdentity,
        ctx: &Pil,
        idx: usize,
    ) -> Result<Self::Error> {
        let constr = &ctx.expressions[i.e.0];
        let expr = eq_zero(self.encode_expression(constr, ctx));
        let fun = self.constr_to_smt_function(i, idx, ctx);
        self.funs
            .push((fun.clone(), Constraint::Identity(i.clone())));
        let fun_def = define_fun(fun, expr);
        self.out(fun_def);
        Ok(())
    }

    fn visit_connection_identity(
        &mut self,
        i: &ConnectionIdentity,
        _: &Pil,
        _: usize,
    ) -> Result<Self::Error> {
        unimplemented!("Found connection identity {:?} which is not supported", i);
    }

    fn visit_permutation_identity(
        &mut self,
        i: &PermutationIdentity,
        _: &Pil,
        _: usize,
    ) -> Result<Self::Error> {
        unimplemented!("Found permutation identity {:?} which is not supported", i);
    }

    fn visit_plookup_identity(
        &mut self,
        i: &PlookupIdentity,
        ctx: &Pil,
        idx: usize,
    ) -> Result<Self::Error> {
        if let Some(ref _id) = i.sel_f {
            unimplemented!("Selectors for 'from' not implemented: {}", i.to_string(ctx));
        }
        if let Some(ref _id) = i.sel_t {
            unimplemented!("Selectors for 'to' not implemented: {}", i.to_string(ctx));
        }

        let row = SMTVariable::new("row".to_string(), SMTSort::Int);

        let mut collector = VariableCollector::new();
        assert_eq!(i.f.len(), i.t.len());
        let conditions = i
            .f
            .iter()
            .zip(i.t.iter())
            .map(|(key, lookup)| {
                collector.visit_expression_id(key, ctx).unwrap();
                let key = self.encode_expression_by_id(key, ctx);
                let lookup = match &ctx.expressions[lookup.0] {
                    Expression::Const(w) => {
                        let (lookup, _) = ctx.get_const_reference(&w.inner);
                        let lookup_name = self
                            .constants
                            .iter()
                            .find(|(name, _)| lookup == IndexedReferenceKey::basic(name))
                            .unwrap_or_else(|| panic!("const {} in plookup is not known", lookup))
                            .0;
                        escape_identifier(lookup_name)
                    }
                    _ => unimplemented!(),
                };
                uf(
                    constant_lookup_function(lookup),
                    vec![row.clone().into(), key],
                )
            })
            .collect();

        let parameters: Vec<_> = collector
            .vars
            .iter()
            .map(|(key, next)| self.key_to_smt_var(key, *next, None))
            .collect();
        let lookup_function =
            SMTFunction::new(format!("lookup_{}", idx), SMTSort::Bool, parameters);
        self.funs
            .push((lookup_function.clone(), Constraint::Lookup(i.clone())));

        let fun_def = define_fun(lookup_function, exists(vec![row], and_vec(conditions)));
        self.out(fun_def);

        Ok(())
    }
}

impl SmtEncoder {
    fn encode_expression(&self, e: &Expression, ctx: &Pil) -> SMTExpr {
        match e {
            Expression::Public(_w) => unimplemented!("public"),

            Expression::Neg(w) => sub(0, self.encode_expression(&w.inner.values[0], ctx)),
            Expression::Add(w) => self.encode_add(&w.inner, ctx),
            Expression::Sub(w) => self.encode_sub(&w.inner, ctx),
            Expression::Mul(w) => self.encode_mul(&w.inner, ctx),
            Expression::Cm(w) => self.encode_cm(&w.inner, ctx),
            Expression::Exp(w) => self.encode_exp(&w.inner, ctx),
            Expression::Number(w) => self.encode_number(&w.inner),
            Expression::Const(w) => self.encode_const(&w.inner, ctx),
        }
    }

    fn encode_expression_by_id(&self, id: &ExpressionId, ctx: &Pil) -> SMTExpr {
        self.encode_expression(&ctx.expressions[id.0], ctx)
    }

    fn encode_add(&self, expr: &Add, ctx: &Pil) -> SMTExpr {
        add(
            self.encode_expression(&expr.values[0], ctx),
            self.encode_expression(&expr.values[1], ctx),
        )
    }

    fn encode_sub(&self, expr: &Sub, ctx: &Pil) -> SMTExpr {
        sub(
            self.encode_expression(&expr.values[0], ctx),
            self.encode_expression(&expr.values[1], ctx),
        )
    }

    fn encode_mul(&self, expr: &Mul, ctx: &Pil) -> SMTExpr {
        mul(
            self.encode_expression(&expr.values[0], ctx),
            self.encode_expression(&expr.values[1], ctx),
        )
    }

    fn encode_cm(&self, expr: &Cm, ctx: &Pil) -> SMTExpr {
        let (key, _) = ctx.get_cm_reference(expr);
        self.key_to_smt_var(&key, expr.next, None).into()
    }

    fn encode_exp(&self, exp: &Exp, ctx: &Pil) -> SMTExpr {
        let (key, _) = ctx.get_exp_reference(exp);
        self.key_to_smt_var(&key, exp.next, None).into()
    }

    fn encode_number(&self, n: &Number) -> SMTExpr {
        literal(n.value.clone(), SMTSort::Int)
    }

    fn encode_const(&self, c: &Const, ctx: &Pil) -> SMTExpr {
        let (key, _) = ctx.get_const_reference(c);
        self.key_to_smt_var(&key, c.next, None).into()
    }
}

#[cfg(test)]
mod test {
    use crate::pilcom;

    use super::*;

    #[test]
    fn encode_byte4() {
        let pil_str = pilcom("pil/zkevm/byte4.pil").unwrap();
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();

        let smt_pil = SmtPil::new(pil, known_constants());

        println!("{}", smt_pil);
    }

    #[test]
    fn encode_arith() {
        let pil_str = pilcom("pil/zkevm/arith.pil").unwrap();
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();

        let smt_pil = SmtPil::new(pil, known_constants());

        println!("{}", smt_pil);
    }
}
