use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fmt;

use crate::ast::*;
use crate::lookup_constants::LookupConstants;
use crate::smt::*;
use crate::visitor::*;

pub struct SmtPil {
    pil: Pil,
    /// Known constants. These can only be used in lookups.
    /// The statement should be SMT functions of the form
    /// (define-fun <constant name> ((row Int) (v Int)) Bool ...)
    /// that return true if and only if the constant value in row `row`
    /// is equal to `v`.
    lookup_constants: LookupConstants,
    in_vars: BTreeSet<String>,
    out_vars: BTreeSet<String>,
    rows: usize,
}

impl SmtPil {
    pub fn new(
        pil: Pil,
        lookup_constants: LookupConstants,
        in_vars: BTreeSet<String>,
        out_vars: BTreeSet<String>,
        rows: usize,
    ) -> Self {
        Self {
            pil,
            lookup_constants,
            in_vars,
            out_vars,
            rows,
        }
    }
}

enum Constraint {
    Identity(PolIdentity),
    Lookup(PlookupIdentity),
}

pub struct SmtEncoder {
    pub smt: Vec<SMTStatement>,
    funs: Vec<SMTFunction>,
    fun_constraints: BTreeMap<String, Constraint>,
    lookup_constants: LookupConstants,
    in_vars: BTreeSet<String>,
    out_vars: BTreeSet<String>,
    rows: usize,
}

impl SmtEncoder {
    pub fn determinism_query(
        pil: &Pil,
        lookup_constants: LookupConstants,
        in_vars: BTreeSet<String>,
        out_vars: BTreeSet<String>,
        rows: usize,
    ) -> Vec<SMTStatement> {
        let mut encoder = SmtEncoder {
            smt: Vec::default(),
            funs: Vec::default(),
            fun_constraints: BTreeMap::default(),
            lookup_constants,
            in_vars,
            out_vars,
            rows,
        };
        encoder.define_constants();
        encoder.visit_pil(pil).unwrap();
        encoder.encode_state_machine_determinism(pil);
        encoder.smt
    }
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
        let smt = SmtEncoder::determinism_query(
            &self.pil,
            self.lookup_constants.clone(),
            self.in_vars.clone(),
            self.out_vars.clone(),
            self.rows,
        );

        writeln!(
            f,
            "; Uncomment the line below to enable proofs\n;(set-option :produce-proofs true)"
        )?;
        writeln!(
            f,
            "{}",
            smt.iter()
                .map(|s| s.as_smt())
                .collect::<Vec<_>>()
                .join("\n")
        )?;

        Ok(())
    }
}

struct VariableCollector {
    vars: BTreeSet<ShiftedPolynomial>,
    consts: BTreeSet<ShiftedPolynomial>,
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
        let pol = cm.to_polynomial(ctx);
        self.vars.insert(pol);
        Ok(())
    }

    fn visit_exp(&mut self, exp: &Exp, ctx: &Pil) -> Result<Self::Error> {
        let pol = exp.to_polynomial(ctx);
        self.vars.insert(pol);
        Ok(())
    }

    fn visit_const(&mut self, c: &Const, ctx: &Pil) -> Result<Self::Error> {
        let pol = c.to_polynomial(ctx);
        self.consts.insert(pol);
        Ok(())
    }
}

pub fn escape_identifier(input: &str) -> String {
    input
        .replace(['.', '['], "_")
        .replace(']', "")
        .replace('\'', "_next")
}

// Some helpers.
fn pol_to_smt_var(pol: &ShiftedPolynomial, suffix: Option<String>) -> SMTVariable {
    let mut key = escape_identifier(&pol.to_string());
    if suffix.is_some() {
        key = format!("{}_{}", key, suffix.unwrap());
    }
    SMTVariable::new(key, SMTSort::Int)
}

fn constr_to_smt_function(i: &PolIdentity, constr_idx: usize, ctx: &Pil) -> SMTFunction {
    let mut collector = VariableCollector::new();
    let constr = &ctx.expressions[i.e.0];
    collector.visit_expression(constr, ctx).unwrap();

    let smt_vars: Vec<_> = collector
        .consts
        .iter()
        .chain(collector.vars.iter())
        .map(|pol| pol_to_smt_var(pol, None))
        .collect();
    SMTFunction::new(format!("constr_{}", constr_idx), SMTSort::Bool, smt_vars)
}

impl SmtEncoder {
    fn define_constants(&mut self) {
        for c in self.lookup_constants.function_definitions() {
            self.out(c);
        }
    }

    /// Encodes a single step / row of the state machine and returns the
    /// function and a vector containing the parameter polynomials except for the
    /// first one which is "row".
    fn encode_state_machine_step(&mut self, p: &Pil) -> (SMTFunction, Vec<ShiftedPolynomial>) {
        // Collect only constants that appear in constraints or
        // LHS of plookups.
        // Constants that appear only in the RHS of a lookup
        // do not need to be a parameter in the state machine.
        let mut const_collector = VariableCollector::new();
        self.fun_constraints.values().for_each(|constr| {
            match constr {
                Constraint::Identity(i) => {
                    // The index 0 below is not used in the visitor.
                    const_collector.visit_polynomial_identity(i, p, 0).unwrap();
                }
                Constraint::Lookup(PlookupIdentity {
                    f,
                    sel_f: None,
                    sel_t: None,
                    ..
                }) => {
                    // The "index" parameter is unused.
                    for e in f {
                        const_collector.visit_expression_id(e, p).unwrap();
                    }
                }
                _ => panic!(),
            }
        });

        let smt_row_arg = SMTVariable::new("row".to_string(), SMTSort::Int);
        // Add `row` to the state machine input.
        let mut smt_vars: Vec<_> = vec![smt_row_arg.clone()];

        // Make SMT vars for the constants.
        smt_vars.extend(
            const_collector
                .consts
                .iter()
                .map(|pol| pol_to_smt_var(pol, None))
                .collect::<Vec<_>>(),
        );

        // Collect `pol commit` variables.
        let mut collector = VariableCollector::new();
        collector.visit_pil(p).unwrap();

        // Make SMT vars for `pol commit` variables.
        smt_vars.extend(
            collector
                .vars
                .iter()
                .map(|pol| pol_to_smt_var(pol, None))
                .collect::<Vec<_>>(),
        );

        // Declare the state machine's function.
        let state_machine_decl =
            SMTFunction::new("state_machine".to_string(), SMTSort::Bool, smt_vars);
        // Add the UF application of every constraint to the body of the state machine.
        // This includes constraints, lookups and constants.
        let body = and_vec(
            [
                self.funs
                    .iter()
                    .map(|f| uf(f.clone(), f.args.iter().map(|v| v.clone().into()).collect()))
                    .collect::<Vec<_>>(),
                const_collector
                    .consts
                    .iter()
                    .filter_map(|c| {
                        let (pol, next) = c.clone().decompose();
                        self.lookup_constants
                            .known_lookup_constant_as_predicate(&pol.into())
                            .map(|f| {
                                uf(
                                    f,
                                    vec![
                                        if next {
                                            add(SMTExpr::from(smt_row_arg.clone()), 1)
                                        } else {
                                            smt_row_arg.clone().into()
                                        },
                                        pol_to_smt_var(c, None).into(),
                                    ],
                                )
                            })
                    })
                    .collect::<Vec<_>>(),
            ]
            .concat(),
        );

        // Warn about constants that are not constrained by a lookup.
        const_collector
            .consts
            .iter()
            .filter(|&c| {
                !self
                    .lookup_constants
                    .is_known_constant(&c.clone().decompose().0.into())
            })
            .for_each(|c| println!("Constant {} used in constraints has no lookup function.", c));

        self.out(define_fun(state_machine_decl.clone(), body));

        (
            state_machine_decl,
            const_collector
                .consts
                .iter()
                .chain(collector.vars.iter())
                .cloned()
                .collect::<Vec<_>>(),
        )
    }

    fn encode_state_machine_unrolled(
        state_machine_decl: SMTFunction,
        in_vars: &BTreeSet<String>,
        all_vars: Vec<ShiftedPolynomial>,
        rows: usize,
        executions: usize,
    ) -> Vec<SMTStatement> {
        let mut decls: BTreeSet<SMTVariable> = BTreeSet::default();
        let mut appls: Vec<SMTExpr> = vec![];
        let mut rows_constrs: Vec<SMTExpr> = vec![];
        let mut next_constrs: Vec<SMTExpr> = vec![];

        // Unroll the state machine `rows` times
        // state_machine(row_i, input_row_i, out_row_i, out_next_row_i)
        (0..rows).for_each(|row| {
            // Create a `row` variable for each row.
            let smt_row = SMTVariable::new(format!("row{}", row), SMTSort::Int);

            // For every sequential pair of rows,
            // add the constraint `(= row (+ prev_row 1))`.
            if row > 0 {
                let smt_prev_row = SMTVariable::new(format!("row{}", row - 1), SMTSort::Int);
                rows_constrs.push(eq(smt_row.clone(), add(smt_prev_row, 1)));
            }

            // Do that for two executions that act on the same inputs
            // but on different syntactic outputs, so that at the end
            // we can query whether they can be different.
            // state_machine(row_i, input_row_i_exec_0, out_row_i_exec_0, out_next_row_i_exec_0)
            // state_machine(row_i, input_row_i_exec_1, out_row_i_exec_1, out_next_row_i_exec_1)
            (0..executions).for_each(|exec| {
                // Create the state machine arguments
                let mut inner_decls: Vec<SMTVariable> = vec![];

                // Add row to the state machine arguments
                inner_decls.push(smt_row.clone());

                all_vars.iter().for_each(|pol| {
                    // Create and declare the variable for this row and execution.
                    let smt_var = pol_to_smt_var(pol, Some(format!("_row{}_exec{}", row, exec)));
                    inner_decls.push(smt_var.clone());

                    // Bind `var` and `next_var` in two sequential rows in the same execution.
                    if row > 0 {
                        if let Some(ref pol_next) = pol.next() {
                            let prev_smt_var = pol_to_smt_var(
                                pol_next,
                                Some(format!("_row{}_exec{}", row - 1, exec)),
                            );
                            decls.insert(prev_smt_var.clone());
                            next_constrs.push(eq(smt_var.clone(), prev_smt_var));
                        }
                    }

                    // Bind two input variables of same row and different execution.
                    if exec > 0 && in_vars.get(&pol_to_smt_var(pol, None).name).is_some() {
                        let other_exec_smt_var =
                            pol_to_smt_var(pol, Some(format!("_row{}_exec{}", row, exec - 1)));
                        assert!(decls.get(&other_exec_smt_var).is_some());
                        next_constrs.push(eq(smt_var, other_exec_smt_var));
                    }
                });

                // Create the `state_machine` function application.
                appls.push(uf(
                    state_machine_decl.clone(),
                    inner_decls
                        .clone()
                        .into_iter()
                        .map(|decl| decl.into())
                        .collect::<Vec<SMTExpr>>(),
                ));

                // Add the state machine arguments of this iteration to the declaration set.
                decls.extend(inner_decls);
            })
        });

        let mut statements: Vec<SMTStatement> = decls.into_iter().map(declare_const).collect();
        statements.push(assert(and_vec(
            vec![rows_constrs, next_constrs, appls].concat(),
        )));
        statements
    }

    fn encode_state_machine_determinism(&mut self, p: &Pil) {
        // Encode the machine for a single step / row
        let (state_machine_decl, all_vars) = self.encode_state_machine_step(p);

        // Unroll it for "rows" rows and two executions.
        self.out_vec(Self::encode_state_machine_unrolled(
            state_machine_decl,
            &self.in_vars,
            all_vars.clone(),
            self.rows,
            2,
        ));

        if !self.out_vars.is_empty() {
            // Create nondeterminism query
            let query = not(and_vec(
                all_vars
                    .iter()
                    .filter(|pol| self.out_vars.get(&pol_to_smt_var(pol, None).name).is_some())
                    .map(|pol| {
                        eq(
                            pol_to_smt_var(pol, Some(format!("_row{}_exec0", self.rows - 1))),
                            pol_to_smt_var(pol, Some(format!("_row{}_exec1", self.rows - 1))),
                        )
                    })
                    .collect::<Vec<_>>(),
            ));

            self.out(assert(query));
        }
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
        let fun = constr_to_smt_function(i, idx, ctx);
        self.funs.push(fun.clone());
        self.fun_constraints
            .insert(fun.name.clone(), Constraint::Identity(i.clone()));
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

        let mut collector = VariableCollector::new();
        assert_eq!(i.f.len(), i.t.len());
        let lhs_exprs: Vec<SMTExpr> =
            i.f.iter()
                .map(|expr| {
                    collector.visit_expression_id(expr, ctx).unwrap();
                    self.encode_expression_by_id(expr, ctx)
                })
                .collect();
        let rhs_constants: Vec<ShiftedPolynomial> =
            i.t.iter()
                .map(|lookup| match &ctx.expressions[lookup.0] {
                    Expression::Const(w) => {
                        let lookup = w.inner.to_polynomial(ctx);
                        if !self.lookup_constants.is_known_constant(&lookup) {
                            panic!("const {} in plookup is not known", lookup);
                        }
                        lookup
                    }
                    _ => unimplemented!(),
                })
                .collect();

        let parameters: Vec<_> = collector
            .vars
            .iter()
            .chain(collector.consts.iter())
            .map(|pol| pol_to_smt_var(pol, None))
            .collect();
        let lookup_function =
            SMTFunction::new(format!("lookup_{}", idx), SMTSort::Bool, parameters);
        self.funs.push(lookup_function.clone());
        self.fun_constraints
            .insert(lookup_function.name.clone(), Constraint::Lookup(i.clone()));

        let fun_def = define_fun(
            lookup_function,
            self.lookup_constants
                .encode_lookup(lhs_exprs, rhs_constants),
        );
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
        let pol = expr.to_polynomial(ctx);
        pol_to_smt_var(&pol, None).into()
    }

    fn encode_exp(&self, expr: &Exp, ctx: &Pil) -> SMTExpr {
        let pol = expr.to_polynomial(ctx);
        pol_to_smt_var(&pol, None).into()
    }

    fn encode_number(&self, n: &Number) -> SMTExpr {
        match n.value.clone().parse::<i64>() {
            Ok(i) if i < 0 => usub(literal((-i).to_string(), SMTSort::Int)),
            _ => literal(n.value.clone(), SMTSort::Int),
        }
    }

    fn encode_const(&self, c: &Const, ctx: &Pil) -> SMTExpr {
        let pol = c.to_polynomial(ctx);
        pol_to_smt_var(&pol, None).into()
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

        let smt_pil = SmtPil::new(
            pil,
            LookupConstants::new(),
            BTreeSet::default(),
            BTreeSet::default(),
            3,
        );

        println!("{}", smt_pil);
    }

    #[test]
    fn encode_arith() {
        let pil_str = pilcom("pil/zkevm/arith.pil").unwrap();
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();

        let smt_pil = SmtPil::new(
            pil,
            LookupConstants::new(),
            BTreeSet::default(),
            BTreeSet::default(),
            3,
        );

        println!("{}", smt_pil);
    }
}
