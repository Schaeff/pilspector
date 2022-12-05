use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fmt;

use crate::{
    validator::Validator,
    visitor::{Result, Visitor},
};

pub type FieldElement = String;

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Pil {
    pub n_commitments: usize,
    pub n_q: usize,
    pub n_im: usize,
    pub n_constants: usize,
    pub publics: Vec<PublicCell>,
    pub references: References,
    pub expressions: Vec<Expression>,
    pub pol_identities: Vec<PolIdentity>,
    pub plookup_identities: Vec<PlookupIdentity>,
    pub permutation_identities: Vec<PermutationIdentity>,
    pub connection_identities: Vec<ConnectionIdentity>,
}

impl Pil {
    pub fn validate(&self) -> Result<String> {
        Validator::default().visit_pil(self)
    }
}

struct PilDisplayer<'a, 'b> {
    f: &'a mut fmt::Formatter<'b>,
}

impl<'a, 'b> Visitor for PilDisplayer<'a, 'b> {
    type Error = fmt::Error;

    fn visit_pil(&mut self, p: &Pil) -> Result<Self::Error> {
        let ctx = p;

        for (key, r) in p.references.iter() {
            write!(self.f, "pol")?;

            write!(self.f, " ")?;

            write!(self.f, "{}", key)?;
            writeln!(self.f)?;
        }

        for i in &p.pol_identities {
            self.visit_polynomial_identity(i, ctx)?;
            writeln!(self.f)?;
        }

        Ok(())
    }

    fn visit_polynomial_identity(&mut self, i: &PolIdentity, ctx: &Pil) -> Result<Self::Error> {
        self.visit_expression(&ctx.expressions[i.e.0], ctx)?;
        write!(self.f, " == 0")
    }

    fn visit_reference_key(&mut self, c: &ReferenceKey, _ctx: &Pil) -> Result<Self::Error> {
        write!(self.f, "{}", c)
    }

    fn visit_add(&mut self, add: &Add, ctx: &Pil) -> Result<Self::Error> {
        write!(self.f, "(")?;
        self.visit_expression(&add.values[0], ctx)?;
        write!(self.f, " + ")?;
        self.visit_expression(&add.values[1], ctx)?;
        write!(self.f, ")")
    }

    fn visit_sub(&mut self, sub: &Sub, ctx: &Pil) -> Result<Self::Error> {
        write!(self.f, "(")?;
        self.visit_expression(&sub.values[0], ctx)?;
        write!(self.f, " - ")?;
        self.visit_expression(&sub.values[1], ctx)?;
        write!(self.f, ")")
    }

    fn visit_mul(&mut self, mul: &Mul, ctx: &Pil) -> Result<Self::Error> {
        write!(self.f, "(")?;
        self.visit_expression(&mul.values[0], ctx)?;
        write!(self.f, " * ")?;
        self.visit_expression(&mul.values[1], ctx)?;
        write!(self.f, ")")
    }

    fn visit_number(&mut self, c: &Number, _ctx: &Pil) -> Result<Self::Error> {
        write!(self.f, "{}", c.value)
    }

    fn visit_next(&mut self, next: &bool, _ctx: &Pil) -> Result<Self::Error> {
        if *next {
            write!(self.f, "'")?;
        }
        Ok(())
    }
}

impl fmt::Display for Pil {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        PilDisplayer { f }.visit_pil(self)
    }
}

pub type ReferenceKey = String;
pub type References = BTreeMap<ReferenceKey, Reference>;
// the index of the expression in the expression list
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
pub struct ExpressionId(pub usize);
// the index of a committed polynomial
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
pub struct CommittedPolynomialId(pub usize);
// the index of a constant polynomial
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
pub struct ConstantPolynomialId(pub usize);
// the index of a public value in the public list
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
pub struct PublicId(pub usize);
// the index of a row
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
pub struct RowId(pub usize);

impl From<usize> for ExpressionId {
    fn from(n: usize) -> Self {
        Self(n)
    }
}

impl From<usize> for ConstantPolynomialId {
    fn from(n: usize) -> Self {
        Self(n)
    }
}

impl From<usize> for CommittedPolynomialId {
    fn from(n: usize) -> Self {
        Self(n)
    }
}

impl From<usize> for PublicId {
    fn from(n: usize) -> Self {
        Self(n)
    }
}

impl From<usize> for RowId {
    fn from(n: usize) -> Self {
        Self(n)
    }
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
#[serde(tag = "type")]
pub enum Reference {
    CmP(ReferenceInner<CommittedPolynomialId>),
    ConstP(ReferenceInner<ConstantPolynomialId>),
    ImP(ReferenceInner<ExpressionId>),
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct ReferenceInner<Id> {
    pub id: Id,
    pub pol_deg: Option<usize>,
    pub is_array: bool,
    // should be present only when `is_array` is `true`
    pub len: Option<usize>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct ComplexReference {
    pub id: CommittedPolynomialId,
    pub pol_deg: Option<usize>,
    pub is_array: bool,
    // should be present only when `is_array` is `true`
    pub len: Option<usize>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct ConstantReference {
    pub id: ConstantPolynomialId,
    pub pol_deg: Option<usize>,
    pub is_array: bool,
    // should be present only when `is_array` is `true`
    pub len: Option<usize>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct PublicCell {
    pol_type: ReferenceType,
    pol_id: CommittedPolynomialId,
    idx: RowId,
    id: usize,
    name: String,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub enum ReferenceType {
    ConstP,
    CmP,
    ImP,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
#[serde(tag = "op")]
pub enum Expression {
    Public(ExpressionWrapper<Public>),
    Neg(ExpressionWrapper<Neg>),
    Exp(ExpressionWrapper<Exp>),
    Add(ExpressionWrapper<Add>),
    Sub(ExpressionWrapper<Sub>),
    Mul(ExpressionWrapper<Mul>),
    Cm(ExpressionWrapper<Cm>),
    Number(ExpressionWrapper<Number>),
    Const(ExpressionWrapper<Const>),
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct ExpressionWrapper<E> {
    // value provided for all expressions
    pub deg: usize,
    #[serde(flatten)]
    pub inner: E,
    // values only provided for expressions in the expression list, not in their children
    #[serde(flatten)]
    pub top: Option<Top>,
}

pub trait Expr: Sized {
    fn deg(self, deg: usize) -> ExpressionWrapper<Self> {
        ExpressionWrapper {
            deg,
            top: None,
            inner: self,
        }
    }
}

impl Expr for Add {}
impl Expr for Mul {}
impl Expr for Sub {}
impl Expr for Cm {}
impl Expr for Public {}
impl Expr for Neg {}
impl Expr for Number {}
impl Expr for Const {}
impl Expr for Exp {}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Top {
    id_q: usize,
    deps: Vec<ExpressionId>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Add {
    pub values: Box<[Expression; 2]>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Sub {
    pub values: Box<[Expression; 2]>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Mul {
    pub values: Box<[Expression; 2]>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Neg {
    pub values: Box<[Expression; 1]>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Number {
    pub value: FieldElement,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Const {
    pub id: ConstantPolynomialId,
    pub next: bool,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Exp {
    pub id: ExpressionId,
    pub next: bool,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Cm {
    pub id: CommittedPolynomialId,
    pub next: bool,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Public {
    pub id: PublicId,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct PolIdentity {
    // expression id, by index in the expression list
    pub e: ExpressionId,
    #[serde(flatten)]
    pub location: Location,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct PlookupIdentity {
    pub f: Vec<ExpressionId>,
    pub t: Vec<ExpressionId>,
    pub sel_f: Option<ExpressionId>,
    pub sel_t: Option<ExpressionId>,
    #[serde(flatten)]
    pub location: Location,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct PermutationIdentity {
    pub f: Vec<ExpressionId>,
    pub t: Vec<ExpressionId>,
    pub sel_f: Option<ExpressionId>,
    pub sel_t: Option<ExpressionId>,
    #[serde(flatten)]
    pub location: Location,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct ConnectionIdentity {
    pub pols: Vec<ExpressionId>,
    pub connections: Vec<ExpressionId>,
    #[serde(flatten)]
    pub location: Location,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Location {
    pub file_name: String,
    pub line: usize,
}

#[cfg(test)]
mod test {
    use super::*;

    mod ser {
        use pretty_assertions::assert_eq;

        fn assert_expression(e: &Expression, expected: &'static str) {
            assert_eq!(
                serde_json::to_value(e).unwrap(),
                serde_json::from_str::<serde_json::Value>(expected).unwrap()
            );
        }

        use super::*;
        #[test]
        fn expression() {
            // serialize a number
            let forty_two = Expression::Number(Number { value: "42".into() }.deg(1));

            assert_expression(&forty_two, r#"{"deg":1,"op":"number","value":"42"}"#);

            // serialize a subtraction of two numbers
            let e = Expression::Sub(
                Sub {
                    values: Box::new([forty_two.clone(), forty_two.clone()]),
                }
                .deg(1),
            );

            assert_expression(
                &e,
                r#"{"deg":1,"op":"sub","values":[{"deg":1,"op":"number","value":"42"},{"deg":1,"op":"number","value":"42"}]}"#,
            );

            // serialize a product of two numbers
            let e = Expression::Mul(
                Mul {
                    values: Box::new([forty_two.clone(), forty_two]),
                }
                .deg(1),
            );

            assert_expression(
                &e,
                r#"{"deg":1,"op":"mul","values":[{"deg":1,"op":"number","value":"42"},{"deg":1,"op":"number","value":"42"}]}"#,
            );

            // serialize a committed polynomial
            let e = Expression::Cm(
                Cm {
                    id: 42.into(),
                    next: true,
                }
                .deg(1),
            );

            assert_expression(&e, r#"{"deg":1,"op":"cm","id":42,"next":true}"#);

            // serialize a const polynomial
            let e = Expression::Const(
                Const {
                    id: 42.into(),
                    next: true,
                }
                .deg(1),
            );

            assert_expression(&e, r#"{"deg":1,"op":"const","id":42,"next":true}"#);
        }
    }

    mod deser {
        use super::*;

        #[test]
        fn expression() {
            // deserialize complex expression

            let expression_str = r#"{
                "op": "sub",
                "deg": 2,
                "values": [
                 {
                  "op": "add",
                  "deg": 1,
                  "values": [
                   {
                    "op": "const",
                    "deg": 1,
                    "id": 0,
                    "next": false
                   },
                   {
                    "op": "const",
                    "deg": 1,
                    "id": 1,
                    "next": false
                   }
                  ]
                 },
                 {
                  "op": "mul",
                  "deg": 2,
                  "values": [
                   {
                    "op": "cm",
                    "deg": 1,
                    "id": 0,
                    "next": false
                   },
                   {
                    "op": "const",
                    "deg": 1,
                    "id": 0,
                    "next": false
                   }
                  ]
                 }
                ]
               }"#;

            let _: Expression = serde_json::from_str(expression_str).unwrap();
        }
    }
}
