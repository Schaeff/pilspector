use crate::{
    ast::{Pil, Expression, PolIdentity},
    visitor::{Result, Visitor},
};

pub struct PatternDetector {
    pattern: Expression,
    occurrences: Vec<Expression>,
}

impl PatternDetector {
    pub fn detect(pil: &Pil) -> Vec<Expression> {
        let pattern: Expression = serde_json::from_str(
            r#"  {
            "op": "sub",
            "deg": 2,
            "values": [
             {
              "op": "mul",
              "deg": 2,
              "values": [
               {
                "op": "cm",
                "deg": 1,
                "id": 28,
                "next": true,
                "symbolic": true
               },
               {
                "op": "sub",
                "deg": 1,
                "values": [
                 {
                  "op": "number",
                  "deg": 0,
                  "value": "1"
                 },
                 {
                  "op": "const",
                  "deg": 1,
                  "id": 8,
                  "next": true,
                  "symbolic": true
                 }
                ]
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
                "id": 29,
                "next": false,
                "symbolic": true
               },
               {
                "op": "sub",
                "deg": 1,
                "values": [
                 {
                  "op": "number",
                  "deg": 0,
                  "value": "1"
                 },
                 {
                  "op": "const",
                  "deg": 1,
                  "id": 8,
                  "next": true,
                  "symbolic": true
                 }
                ]
               }
              ]
             }
            ]
           }"#,
        )
        .unwrap();

        let mut detector = PatternDetector { pattern, occurrences: vec![] };
        detector.visit_pil(&pil).unwrap();

        detector.occurrences
    }
}

impl Visitor for PatternDetector {
    type Error = String;

    fn visit_polynomial_identity(&mut self, i: &PolIdentity, ctx: &Pil) -> Result<Self::Error> {
        let e = ctx.get_expression(&i.e);

        if *e == self.pattern {
            self.occurrences.push(e.clone());
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn detect_pattern_in_binary() {
        let pil_str = std::fs::read_to_string("binary.pil.json").unwrap();
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();

        println!("occurrences {:#?}", &PatternDetector::detect(&pil));
    }
}
