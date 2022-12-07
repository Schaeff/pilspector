use std::path::PathBuf;

pub mod ast;
mod displayer;
mod smt;
pub mod smt_encoder;
mod validator;
mod visitor;

/// get the path for a compiled PIL file
fn pil_json(f: &str) -> String {
    std::fs::read_to_string(
        PathBuf::from(env!("OUT_DIR"))
            .join("pil")
            .join(f)
            .with_extension("pil.json"),
    )
    .unwrap()
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ast::Pil;

    #[test]
    fn parse_main() {
        let pil_str = pil_json("zkevm/main");
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();
        pil.validate().unwrap();
    }

    #[test]
    fn display_adder() {
        let pil_str = pil_json("adder");
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();
        println!("{}", pil);
    }

    #[test]
    fn display_main() {
        let pil_str = pil_json("zkevm/main");
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();
        println!("{}", pil);
    }
}
