mod ast;
mod displayer;
mod smt_encoder;
mod validator;
mod visitor;

#[cfg(test)]
mod test {
    use crate::ast::Pil;

    #[test]
    fn parse_main() {
        let pil_str = std::fs::read_to_string("main.pil.json").unwrap();
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();
        pil.validate().unwrap();
    }

    #[test]
    fn display_adder() {
        let pil_str = std::fs::read_to_string("adder.pil.json").unwrap();
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();
        println!("{}", pil);
    }

    #[test]
    fn display_multiplier() {
        let pil_str = std::fs::read_to_string("multiplier.pil.json").unwrap();
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();
        println!("{}", pil);
    }

    #[test]
    fn display_main() {
        let pil_str = std::fs::read_to_string("main.pil.json").unwrap();
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();
        println!("{}", pil);
    }
}
