use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fmt;

use crate::{
    displayer::PilDisplayer,
    validator::Validator,
    visitor::{Result, Visitor},
};

pub type FieldElement = String;

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
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

pub trait ToPolynomial {
    fn to_polynomial(&self, ctx: &Pil) -> ShiftedPolynomial;
}

impl ToPolynomial for Cm {
    fn to_polynomial(&self, ctx: &Pil) -> ShiftedPolynomial {
        let (key, r) = ctx
            .references
            .iter()
            .filter_map(|(key, r)| match r {
                Polynomials::CmP(r) => (self.id.0 >= r.id.0
                    && self.id.0 < r.id.0 + r.len.unwrap_or(1))
                .then_some((key, r)),
                _ => None,
            })
            .next()
            .unwrap();

        Polynomial {
            key: key.clone(),
            index: r.len.map(|_| self.id.0 - r.id.0),
        }
        .with_next(self.next)
    }
}

impl ToPolynomial for Const {
    fn to_polynomial(&self, ctx: &Pil) -> ShiftedPolynomial {
        let (key, r) = ctx
            .references
            .iter()
            .filter_map(|(key, r)| match r {
                Polynomials::ConstP(r) => (self.id.0 >= r.id.0
                    && self.id.0 < r.id.0 + r.len.unwrap_or(1))
                .then_some((key, r)),
                _ => None,
            })
            .next()
            .unwrap();

        Polynomial {
            key: key.clone(),
            index: r.len.map(|_| self.id.0 - r.id.0),
        }
        .with_next(self.next)
    }
}

impl ToPolynomial for Exp {
    fn to_polynomial(&self, ctx: &Pil) -> ShiftedPolynomial {
        let (key, r) = ctx
            .references
            .iter()
            .filter_map(|(key, r)| match r {
                Polynomials::ImP(r) => (self.id.0 >= r.id.0
                    && self.id.0 < r.id.0 + r.len.unwrap_or(1))
                .then_some((key, r)),
                _ => None,
            })
            .next()
            .unwrap();

        Polynomial {
            key: key.clone(),
            index: r.len.map(|_| self.id.0 - r.id.0),
        }
        .with_next(self.next)
    }
}

impl Pil {
    /// get all polynomials for a given name: all array accesses, with and without `next`
    pub fn get_polynomials(&self, key: &Name) -> Vec<ShiftedPolynomial> {
        let r = &self.references[key];

        [false, true]
            .iter()
            .flat_map(|next| match r.len() {
                // generate `n` keys for arrays of size `n`
                Some(len) => (0..len)
                    .map(|index| Polynomial::array_element(key, index).with_next(*next))
                    .collect(),
                // generate 1 key for non-array polynomials
                None => vec![Polynomial::basic(key).with_next(*next)],
            })
            .collect()
    }
}

impl Pil {
    #[allow(unused)]
    pub fn validate(&self) -> Result<String> {
        Validator::default().visit_pil(self)
    }
}

impl fmt::Display for Pil {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut displayer = PilDisplayer::default();
        displayer.visit_pil(self).unwrap();
        write!(f, "{}", String::from_utf8(displayer.f).unwrap())
    }
}

pub trait ToStringWithContext {
    fn to_string(&self, context: &Pil) -> String;
}

impl ToStringWithContext for PolIdentity {
    fn to_string(&self, context: &Pil) -> String {
        let mut displayer = PilDisplayer::default();
        displayer
            .visit_polynomial_identity(self, context, 0)
            .unwrap();
        String::from_utf8(displayer.f).unwrap()
    }
}

impl ToStringWithContext for PlookupIdentity {
    fn to_string(&self, context: &Pil) -> String {
        let mut displayer = PilDisplayer::default();
        displayer.visit_plookup_identity(self, context, 0).unwrap();
        String::from_utf8(displayer.f).unwrap()
    }
}

impl ToStringWithContext for PermutationIdentity {
    fn to_string(&self, context: &Pil) -> String {
        let mut displayer = PilDisplayer::default();
        displayer
            .visit_permutation_identity(self, context, 0)
            .unwrap();
        String::from_utf8(displayer.f).unwrap()
    }
}

impl ToStringWithContext for ConnectionIdentity {
    fn to_string(&self, context: &Pil) -> String {
        let mut displayer = PilDisplayer::default();
        displayer
            .visit_connection_identity(self, context, 0)
            .unwrap();
        String::from_utf8(displayer.f).unwrap()
    }
}

impl ToStringWithContext for Expression {
    fn to_string(&self, context: &Pil) -> String {
        let mut displayer = PilDisplayer::default();
        displayer.visit_expression(self, context).unwrap();
        String::from_utf8(displayer.f).unwrap()
    }
}

pub type PublicCellKey = String;
pub type Name = String;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ShiftedPolynomial {
    pub pol: Polynomial,
    pub next: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Polynomial {
    key: Name,
    index: Option<usize>,
}

impl From<Polynomial> for ShiftedPolynomial {
    fn from(pol: Polynomial) -> Self {
        ShiftedPolynomial { pol, next: false }
    }
}

impl ShiftedPolynomial {
    // shift this polynomial if it's not already shifted
    pub fn next(&self) -> Option<Self> {
        (!self.next).then(|| Self {
            next: true,
            ..self.clone()
        })
    }

    pub fn polynomial(&self) -> &Polynomial {
        &self.pol
    }

    pub fn decompose(self) -> (Polynomial, bool) {
        (self.pol, self.next)
    }
}

impl Polynomial {
    pub fn next(self) -> ShiftedPolynomial {
        self.with_next(true)
    }

    pub fn with_next(self, next: bool) -> ShiftedPolynomial {
        ShiftedPolynomial { pol: self, next }
    }
}

impl Polynomial {
    pub fn basic<S: Into<Name>>(key: S) -> Self {
        Self {
            key: key.into(),
            index: None,
        }
    }

    pub fn array_element<S: Into<Name>>(key: S, index: usize) -> Self {
        Self {
            key: key.into(),
            index: Some(index),
        }
    }

    pub fn index(&self) -> Option<usize> {
        self.index
    }

    pub fn key(&self) -> &Name {
        &self.key
    }
}

impl fmt::Display for ShiftedPolynomial {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.pol)?;
        if self.next {
            write!(f, "'")?;
        }
        Ok(())
    }
}

impl fmt::Display for Polynomial {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.key)?;
        if let Some(index) = self.index {
            write!(f, "[{}]", index)?;
        }
        Ok(())
    }
}

pub type References = BTreeMap<Name, Polynomials>;
// the index of the expression in the expression list
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Copy, Hash)]
pub struct ExpressionId(pub usize);
// the index of a committed polynomial
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Copy, Hash)]
pub struct CommittedPolynomialId(pub usize);
// the index of a constant polynomial
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Copy, Hash)]
pub struct ConstantPolynomialId(pub usize);
// the index of a public value in the public list
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Copy, Hash)]
pub struct PublicId(pub usize);
// the index of a row
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Copy, Hash)]
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

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
#[serde(tag = "type")]
pub enum Polynomials {
    CmP(PolynomialsInner<CommittedPolynomialId>),
    ConstP(PolynomialsInner<ConstantPolynomialId>),
    ImP(PolynomialsInner<ExpressionId>),
}

impl Polynomials {
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> Option<usize> {
        match self {
            Polynomials::CmP(r) => r.len,
            Polynomials::ConstP(r) => r.len,
            Polynomials::ImP(r) => r.len,
        }
    }
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct PolynomialsInner<Id> {
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

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct PublicCell {
    // this must be "cmP", checked in the validator
    pub pol_type: String,
    pub pol_id: CommittedPolynomialId,
    pub idx: RowId,
    // this seems to be the id of this cell in the list of public cells, seems redundant
    pub id: usize,
    pub name: PublicCellKey,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
#[serde(tag = "op")]
pub enum Expression {
    Public(ExpressionWrapper<Public>),
    Neg(ExpressionWrapper<Neg>),
    Add(ExpressionWrapper<Add>),
    Sub(ExpressionWrapper<Sub>),
    Mul(ExpressionWrapper<Mul>),
    Cm(ExpressionWrapper<Cm>),
    Exp(ExpressionWrapper<Exp>),
    Number(ExpressionWrapper<Number>),
    Const(ExpressionWrapper<Const>),
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
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

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Top {
    id_q: usize,
    deps: Vec<ExpressionId>,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Add {
    pub values: Box<[Expression; 2]>,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Sub {
    pub values: Box<[Expression; 2]>,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Mul {
    pub values: Box<[Expression; 2]>,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Neg {
    pub values: Box<[Expression; 1]>,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Number {
    pub value: FieldElement,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Const {
    pub id: ConstantPolynomialId,
    pub next: bool,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Exp {
    pub id: ExpressionId,
    pub next: bool,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Cm {
    pub id: CommittedPolynomialId,
    pub next: bool,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct Public {
    pub id: PublicId,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct PolIdentity {
    // expression id, by index in the expression list, referring to the expression which must equal 0
    pub e: ExpressionId,
    #[serde(flatten)]
    pub location: Location,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct PlookupIdentity {
    /// What we are looking up
    pub f: Vec<ExpressionId>,
    /// Where we are looking it up in
    pub t: Vec<ExpressionId>,
    /// Selector for what we are looking up,
    /// removes rows where this expresison is zero,
    /// might alter the value if it is not one.
    pub sel_f: Option<ExpressionId>,
    /// Selector for where we are looking it up in
    /// removes rows where this expresison is zero,
    /// might alter the value if it is not one.
    pub sel_t: Option<ExpressionId>,
    #[serde(flatten)]
    pub location: Location,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
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

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub struct ConnectionIdentity {
    pub pols: Vec<ExpressionId>,
    pub connections: Vec<ExpressionId>,
    #[serde(flatten)]
    pub location: Location,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
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

            // serialize a intermediate polynomial expression
            let e = Expression::Exp(
                Exp {
                    id: 42.into(),
                    next: true,
                }
                .deg(1),
            );

            assert_expression(&e, r#"{"deg":1,"op":"exp","id":42,"next":true}"#);

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
