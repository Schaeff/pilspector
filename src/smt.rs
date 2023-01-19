#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SMTSort {
    Bool,
    Int,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SMTVariable {
    pub name: String,
    pub sort: SMTSort,
}

impl SMTVariable {
    pub fn new(name: String, sort: SMTSort) -> Self {
        SMTVariable { name, sort }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SMTFunction {
    pub name: String,
    pub sort: SMTSort,
    pub args: Vec<SMTVariable>,
}

impl SMTFunction {
    pub fn new(name: String, sort: SMTSort, args: Vec<SMTVariable>) -> Self {
        SMTFunction { name, sort, args }
    }
}

/// We keep the SMT expressions loose and runtime based for now.
/// A potential future refactor may add compile time guarantees
/// that illegal expressions cannot be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SMTExpr {
    pub op: SMTOp,
    pub args: Vec<SMTExpr>,
}

impl From<u64> for SMTExpr {
    fn from(input: u64) -> SMTExpr {
        SMTExpr {
            op: SMTOp::Literal(format!("{}", input), SMTSort::Int),
            args: vec![],
        }
    }
}

pub fn signed_to_smt(input: i64) -> SMTExpr {
    if input < 0 {
        usub(literal((-input).to_string(), SMTSort::Int))
    } else {
        SMTExpr {
            op: SMTOp::Literal(format!("{}", input), SMTSort::Int),
            args: vec![],
        }
    }
}

impl From<SMTVariable> for SMTExpr {
    fn from(input: SMTVariable) -> SMTExpr {
        SMTExpr {
            op: SMTOp::Variable(input),
            args: vec![],
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SMTStatement {
    Assert(SMTExpr),
    DeclareConst(SMTVariable),
    DeclareFun(SMTVariable, Vec<SMTSort>),
    DefineConst(SMTVariable, SMTExpr),
    DefineFun(SMTVariable, Vec<SMTVariable>, SMTExpr),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SMTOp {
    Eq,
    Not,
    And,
    Or,
    Ite,
    Implies,
    Add,
    Sub,
    USub,
    Mul,
    Div,
    Mod,
    Lt,
    Le,
    Gt,
    Ge,
    Let(Vec<(String, SMTExpr)>),
    Exists(Vec<SMTVariable>),
    Literal(String, SMTSort),
    Variable(SMTVariable),
    UF(SMTFunction), // TODO We should have a specialized SMTFunction
}

// SMT expression builders

pub fn eq<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Eq,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn neq<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    not(eq(lhs, rhs))
}

pub fn eq_zero<L: Into<SMTExpr>>(expr: L) -> SMTExpr {
    eq(expr, 0)
}

pub fn neq_zero<L: Into<SMTExpr>>(expr: L) -> SMTExpr {
    neq(expr, 0)
}

pub fn not<L: Into<SMTExpr>>(expr: L) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Not,
        args: vec![expr.into()],
    }
}

/*
pub fn and<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::And,
        args: vec![lhs.into(), rhs.into()],
    }
}
*/

pub fn and_vec(args: Vec<impl Into<SMTExpr>>) -> SMTExpr {
    match args.len() {
        0 => literal_true(),
        1 => args.into_iter().next().unwrap().into(),
        _ => SMTExpr {
            op: SMTOp::And,
            args: args.into_iter().map(|a| a.into()).collect(),
        },
    }
}

/*
pub fn or<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Or,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn or_vec(args: Vec<SMTExpr>) -> SMTExpr {
    match args.len() {
        0 => literal_false(),
        1 => args.into_iter().next().unwrap(),
        _ => SMTExpr {
            op: SMTOp::Or,
            args,
        },
    }
}
*/
pub fn ite<C: Into<SMTExpr>, T: Into<SMTExpr>, F: Into<SMTExpr>>(
    cond: C,
    true_term: T,
    false_term: F,
) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Ite,
        args: vec![cond.into(), true_term.into(), false_term.into()],
    }
}

pub fn implies(premise: impl Into<SMTExpr>, conclusion: impl Into<SMTExpr>) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Implies,
        args: vec![premise.into(), conclusion.into()],
    }
}

pub fn let_smt(aliases: Vec<(String, SMTExpr)>, inner: SMTExpr) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Let(aliases),
        args: vec![inner],
    }
}

pub fn exists(vars: Vec<SMTVariable>, inner: SMTExpr) -> SMTExpr {
    match vars.len() {
        0 => inner,
        _ => SMTExpr {
            op: SMTOp::Exists(vars),
            args: vec![inner],
        },
    }
}

pub fn add<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Add,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn sub<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Sub,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn usub<L: Into<SMTExpr>>(lhs: L) -> SMTExpr {
    SMTExpr {
        op: SMTOp::USub,
        args: vec![lhs.into()],
    }
}

pub fn mul<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Mul,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn div<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Div,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn modulo<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Mod,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn lt<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Lt,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn le<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Le,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn gt<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Gt,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn ge<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Ge,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn literal(lit: String, sort: SMTSort) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Literal(lit, sort),
        args: vec![],
    }
}

pub fn uf(function: SMTFunction, args: Vec<SMTExpr>) -> SMTExpr {
    SMTExpr {
        op: SMTOp::UF(function),
        args,
    }
}

fn literal_bool(lit: String) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Literal(lit, SMTSort::Bool),
        args: vec![],
    }
}

pub fn literal_true() -> SMTExpr {
    literal_bool("true".to_string())
}

/*
pub fn literal_false() -> SMTExpr {
    literal_bool("false".to_string())
}
*/

// SMT statement builders
pub fn assert(expr: SMTExpr) -> SMTStatement {
    SMTStatement::Assert(expr)
}

pub fn declare_const(var: SMTVariable) -> SMTStatement {
    SMTStatement::DeclareConst(var)
}

pub fn declare_fun(var: SMTVariable, sorts: Vec<SMTSort>) -> SMTStatement {
    SMTStatement::DeclareFun(var, sorts)
}

/*
pub fn define_const(var: SMTVariable, val: SMTExpr) -> SMTStatement {
    SMTStatement::DefineConst(var, val)
}
*/

pub fn define_fun(fun: SMTFunction, val: SMTExpr) -> SMTStatement {
    SMTStatement::DefineFun(SMTVariable::new(fun.name, fun.sort), fun.args, val)
}

// Format stuff

pub trait SMTFormat {
    fn as_smt(&self) -> String;
}

impl SMTFormat for SMTSort {
    fn as_smt(&self) -> String {
        match self {
            SMTSort::Bool => "Bool".to_string(),
            SMTSort::Int => "Int".to_string(),
        }
    }
}

impl SMTFormat for SMTVariable {
    fn as_smt(&self) -> String {
        self.name.clone()
    }
}

impl SMTFormat for SMTExpr {
    fn as_smt(&self) -> String {
        match &self.op {
            SMTOp::Eq => {
                assert!(self.args.len() == 2);
                format!(
                    "\n\t\t(= {} {})",
                    self.args[0].as_smt(),
                    self.args[1].as_smt()
                )
            }
            SMTOp::Not => {
                assert!(self.args.len() == 1);
                format!("(not {})", self.args[0].as_smt())
            }
            SMTOp::And => {
                assert!(self.args.len() >= 2);
                format!("(and {})", self.args.as_smt())
            }
            SMTOp::Or => {
                assert!(self.args.len() >= 2);
                format!("(or {})", self.args.as_smt())
            }
            SMTOp::Ite => {
                assert!(self.args.len() == 3);
                format!(
                    "(ite {} {} {})",
                    self.args[0].as_smt(),
                    self.args[1].as_smt(),
                    self.args[2].as_smt()
                )
            }
            SMTOp::Implies => {
                assert!(self.args.len() == 2);
                format!("(=> {} {})", self.args[0].as_smt(), self.args[1].as_smt(),)
            }
            SMTOp::Add => {
                assert!(self.args.len() == 2);
                format!("(+ {} {})", self.args[0].as_smt(), self.args[1].as_smt())
            }
            SMTOp::Sub => {
                assert!(self.args.len() == 2);
                format!("(- {} {})", self.args[0].as_smt(), self.args[1].as_smt())
            }
            SMTOp::USub => {
                assert!(self.args.len() == 1);
                format!("(- {})", self.args[0].as_smt())
            }
            SMTOp::Mul => {
                assert!(self.args.len() == 2);
                format!("(* {} {})", self.args[0].as_smt(), self.args[1].as_smt())
            }
            SMTOp::Div => {
                assert!(self.args.len() == 2);
                format!("(div {} {})", self.args[0].as_smt(), self.args[1].as_smt())
            }
            SMTOp::Mod => {
                assert!(self.args.len() == 2);
                format!("(mod {} {})", self.args[0].as_smt(), self.args[1].as_smt())
            }
            SMTOp::Lt => {
                assert!(self.args.len() == 2);
                format!("(< {} {})", self.args[0].as_smt(), self.args[1].as_smt())
            }
            SMTOp::Le => {
                assert!(self.args.len() == 2);
                format!("(<= {} {})", self.args[0].as_smt(), self.args[1].as_smt())
            }
            SMTOp::Gt => {
                assert!(self.args.len() == 2);
                format!("(> {} {})", self.args[0].as_smt(), self.args[1].as_smt())
            }
            SMTOp::Ge => {
                assert!(self.args.len() == 2);
                format!("(>= {} {})", self.args[0].as_smt(), self.args[1].as_smt())
            }
            SMTOp::Let(aliases) => {
                format!(
                    "(let ({}) {})",
                    aliases
                        .iter()
                        .map(|(alias, expr)| format!("({} {})", alias, expr.as_smt()))
                        .collect::<Vec<String>>()
                        .join(" "),
                    self.args[0].as_smt()
                )
            }
            SMTOp::Exists(vars) => {
                assert!(self.args.len() == 1);
                format!(
                    "(exists ({}) {})",
                    vars.iter()
                        .map(|var| format!("({} {})", var.name, var.sort.as_smt()))
                        .collect::<Vec<String>>()
                        .join(" "),
                    self.args[0].as_smt(),
                )
            }
            SMTOp::Literal(lit, sort) => match sort {
                SMTSort::Bool => lit.to_string(),
                SMTSort::Int => lit.to_string(),
            },
            SMTOp::Variable(var) if self.args.is_empty() => var.as_smt(),
            SMTOp::Variable(var) => format!("({} {})", var.as_smt(), self.args.as_smt()),

            SMTOp::UF(function) => {
                format!("\n\t\t({} {})", function.name, self.args.as_smt())
            }
        }
    }
}

impl SMTFormat for SMTStatement {
    fn as_smt(&self) -> String {
        match self {
            SMTStatement::Assert(expr) => format!("(assert {})", expr.as_smt()),
            SMTStatement::DeclareConst(var) => {
                format!("(declare-const {} {})", var.name, var.sort.as_smt())
            }
            SMTStatement::DeclareFun(var, sorts) => format!(
                "(declare-fun {} ({}) {})",
                var.name,
                sorts.as_smt(),
                var.sort.as_smt()
            ),
            SMTStatement::DefineConst(var, expr) => format!(
                "(define-const {} {} {})",
                var.name,
                var.sort.as_smt(),
                expr.as_smt()
            ),
            SMTStatement::DefineFun(var, vars, expr) => format!(
                "(define-fun {} ({}) {} {})\n",
                var.name,
                vars.iter()
                    .map(|var| format!("({} {})", var.name, var.sort.as_smt()))
                    .collect::<Vec<String>>()
                    .join(" "),
                var.sort.as_smt(),
                expr.as_smt()
            ),
        }
    }
}

impl<T: SMTFormat> SMTFormat for Vec<T> {
    fn as_smt(&self) -> String {
        self.iter()
            .map(SMTFormat::as_smt)
            .collect::<Vec<_>>()
            .join(" ")
    }
}
