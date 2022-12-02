use serde::{Deserialize, Serialize};
use std::collections::HashMap;

pub type FieldElement = String;

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Pil {
    n_commitments: usize,
    n_q: usize,
    n_im: usize,
    n_constants: usize,
    publics: Vec<PublicCell>,
    references: References,
    expressions: Vec<Expression>,
    pol_identities: Vec<PolIdentity>,
    plookup_identities: Vec<PlookupIdentity>,
    permutation_identities: Vec<PermutationIdentity>,
    connection_identities: Vec<ConnectionIdentity>,
}

pub type ReferenceKey = String;
pub type References = HashMap<ReferenceKey, ReferenceInner>;
// the index of a polynomial
pub type PolynomialId = usize;
// the index of a row
pub type RowId = usize;

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct ReferenceInner {
    _type: ReferenceType,
    id: PolynomialId,
    pol_deg: Option<usize>,
    is_array: bool,
    // should be present only when `is_array` is `true`
    len: Option<usize>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct PublicCell {
    pol_type: ReferenceType,
    pol_id: PolynomialId,
    idx: RowId,
    id: usize,
    name: String,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
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
    Neg(ExpressionWrapper<Value>),
    Exp(ExpressionWrapper<Exp>),
    Add(ExpressionWrapper<Values>),
    Sub(ExpressionWrapper<Values>),
    Mul(ExpressionWrapper<Values>),
    Cm(ExpressionWrapper<Cm>),
    Number(ExpressionWrapper<Number>),
    Const(ExpressionWrapper<Const>),
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct ExpressionWrapper<E> {
    // value provided for all expressions
    deg: usize,
    #[serde(flatten)]
    inner: E,
    // values only provided for expressions in the expression list, not in their children
    #[serde(flatten)]
    top: Option<Top>,
}

trait Expr: Sized {
    fn deg(self, deg: usize) -> ExpressionWrapper<Self> {
        ExpressionWrapper {
            deg,
            top: None,
            inner: self,
        }
    }
}

impl Expr for Values {}
impl Expr for Cm {}
impl Expr for Public {}
impl Expr for Value {}
impl Expr for Number {}
impl Expr for Const {}
impl Expr for Exp {}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Top {
    id_q: usize,
    deps: Vec<PolynomialId>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Values {
    values: Box<[Expression; 2]>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Value {
    values: Box<[Expression; 1]>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Number {
    value: FieldElement,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Const {
    id: PolynomialId,
    next: bool,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Exp {
    id: PolynomialId,
    next: bool,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Cm {
    id: PolynomialId,
    next: bool,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Public {
    id: PolynomialId,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct PolIdentity {
    e: PolynomialId,
    #[serde(flatten)]
    location: Location,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct PlookupIdentity {
    f: Vec<PolynomialId>,
    t: Vec<PolynomialId>,
    sel_f: Option<PolynomialId>,
    sel_t: Option<PolynomialId>,
    #[serde(flatten)]
    location: Location,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct PermutationIdentity {
    f: Vec<PolynomialId>,
    t: Vec<PolynomialId>,
    sel_f: Option<PolynomialId>,
    sel_t: Option<PolynomialId>,
    #[serde(flatten)]
    location: Location,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct ConnectionIdentity {
    pols: Vec<PolynomialId>,
    connections: Vec<PolynomialId>,
    #[serde(flatten)]
    location: Location,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Location {
    file_name: String,
    line: usize,
}

#[cfg(test)]
mod test {
    use super::*;

    mod ser {
        use pretty_assertions::assert_eq;

        fn assert_expression(e: &Expression, expected: &'static str) {
            assert_eq!(
                serde_json::to_value(&e).unwrap(),
                serde_json::from_str::<serde_json::Value>(&expected).unwrap()
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
                Values {
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
                Values {
                    values: Box::new([forty_two.clone(), forty_two.clone()]),
                }
                .deg(1),
            );

            assert_expression(
                &e,
                r#"{"deg":1,"op":"mul","values":[{"deg":1,"op":"number","value":"42"},{"deg":1,"op":"number","value":"42"}]}"#,
            );

            // serialize a committed polynomial
            let e = Expression::Cm(Cm { id: 42, next: true }.deg(1));

            assert_expression(&e, r#"{"deg":1,"op":"cm","id":42,"next":true}"#);

            // serialize a const polynomial
            let e = Expression::Const(Const { id: 42, next: true }.deg(1));

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
