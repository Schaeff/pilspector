pub mod ast;
mod constants;
mod displayer;
mod smt;
pub mod smt_encoder;
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

    #[test]
    fn display_arrays() {
        let pil_str = std::fs::read_to_string("arrays.pil.json").unwrap();
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();
        assert_eq!(&pil.to_string(), "pol commit Array.x[2];\npol constant Array.y[2];\n((Array.x[0] * Array.y[1]) - (Array.x[1] * Array.y[0])) == 0\n");
    }
}
