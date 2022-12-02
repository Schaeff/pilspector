mod ast;

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod test {
    use crate::ast::Pil;

    #[test]
    fn parse_binary() {
        let pil_str = std::fs::read_to_string("main.pil.json").unwrap();

        let _: Pil = serde_json::from_str(&pil_str).unwrap();
    }
}
