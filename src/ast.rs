use serde::{Deserialize, Serialize};
use serde_json::Value;
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
    publics: Vec<Value>,
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
pub enum ReferenceType {
    ConstP,
    CmP,
    ImP,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Expression {
    deg: usize,
    #[serde(flatten)]
    inner: ExpressionInner,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
#[serde(tag = "op")]
pub enum ExpressionInner {
    Add(Values),
    Sub(Values),
    Mul(Values),
    Cm(Cm),
    Number(Number),
    Const(Const),
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
pub struct Cm {
    id: PolynomialId,
    next: bool,
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
    sel_f: Option<Value>,
    sel_t: Option<Value>,
    #[serde(flatten)]
    location: Location,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct PermutationIdentity {
    f: Vec<PolynomialId>,
    t: Vec<PolynomialId>,
    sel_f: Option<Value>,
    sel_t: Option<Value>,
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
    use pretty_assertions::assert_eq;

    #[test]
    fn expression() {
        // serialize a number
        let forty_two = Expression {
            deg: 1,
            inner: ExpressionInner::Number(Number { value: "42".into() }),
        };

        assert_eq!(
            serde_json::to_string(&forty_two).unwrap(),
            r#"{"deg":1,"op":"number","value":"42"}"#
        );

        // serialize a subtraction of two numbers
        let e = Expression {
            deg: 1,
            inner: ExpressionInner::Sub(Values {
                values: Box::new([forty_two.clone(), forty_two.clone()]),
            }),
        };

        assert_eq!(
            serde_json::to_string(&e).unwrap(),
            r#"{"deg":1,"op":"sub","values":[{"deg":1,"op":"number","value":"42"},{"deg":1,"op":"number","value":"42"}]}"#
        );

        // serialize a product of two numbers
        let e = Expression {
            deg: 1,
            inner: ExpressionInner::Mul(Values {
                values: Box::new([forty_two.clone(), forty_two.clone()]),
            }),
        };

        assert_eq!(
            serde_json::to_string(&e).unwrap(),
            r#"{"deg":1,"op":"mul","values":[{"deg":1,"op":"number","value":"42"},{"deg":1,"op":"number","value":"42"}]}"#
        );

        // serialize a committed polynomial
        let e = Expression {
            deg: 1,
            inner: ExpressionInner::Cm(Cm { id: 42, next: true }),
        };

        assert_eq!(
            serde_json::to_string(&e).unwrap(),
            r#"{"deg":1,"op":"cm","id":42,"next":true}"#
        );

        // serialize a const polynomial
        let e = Expression {
            deg: 1,
            inner: ExpressionInner::Const(Const { id: 42, next: true }),
        };

        assert_eq!(
            serde_json::to_string(&e).unwrap(),
            r#"{"deg":1,"op":"const","id":42,"next":true}"#
        );

        // serialize two expressions
        let e = vec![
            Expression {
                deg: 1,
                inner: ExpressionInner::Const(Const { id: 42, next: true }),
            },
            Expression {
                deg: 1,
                inner: ExpressionInner::Const(Const { id: 42, next: true }),
            },
        ];

        assert_eq!(
            serde_json::to_string(&e).unwrap(),
            r#"[{"deg":1,"op":"const","id":42,"next":true},{"deg":1,"op":"const","id":42,"next":true}]"#
        );
    }
}
