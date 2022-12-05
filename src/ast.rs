use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fmt;

use crate::{
    displayer::PilDisplayer,
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
    // the cells `(polynomial, row)` which are exposed to the verifier
    pub publics: Vec<PublicCell>,
    // all polynomials in a map
    pub references: References,
    // all expressions in a list
    pub expressions: Vec<Expression>,
    // all expressions which must equal 0 (`==` operator)
    pub pol_identities: Vec<PolIdentity>,
    // all lookups which must succeed (`in` operator)
    pub plookup_identities: Vec<PlookupIdentity>,
    // all permutations which must hold (`is` operator)
    pub permutation_identities: Vec<PermutationIdentity>,
    // all connections which must hold (`connect` operator)
    pub connection_identities: Vec<ConnectionIdentity>,
}

impl Pil {
    #[allow(unused)]
    pub fn validate(&self) -> Result<String> {
        Validator::default().visit_pil(self)
    }
}

impl fmt::Display for Pil {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        PilDisplayer { f }.visit_pil(self)
    }
}

pub type PublicCellKey = String;
pub type ReferenceKey = String;
pub type References = BTreeMap<ReferenceKey, Reference>;
// the index of the expression in the expression list
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Copy)]
pub struct ExpressionId(pub usize);
// the index of a committed polynomial
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Copy)]
pub struct CommittedPolynomialId(pub usize);
// the index of a constant polynomial
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Copy)]
pub struct ConstantPolynomialId(pub usize);
// the index of a public value in the public list
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Copy)]
pub struct PublicId(pub usize);
// the index of a row
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Copy)]
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
    // this must be "cmP"
    pub pol_type: String,
    pub pol_id: CommittedPolynomialId,
    pub idx: RowId,
    // this seems to be the id of this cell in the list of public cells, seems redundant
    pub id: usize,
    pub name: PublicCellKey,
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
