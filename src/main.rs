mod ast;

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod test {
    use crate::ast::Pil;

    #[test]
    fn parse_binary() {
        let binary_pil_str = std::fs::read_to_string("nine2one.pil.json").unwrap();

        let pil: Pil = serde_json::from_str(&binary_pil_str)
            .map_err(|e| {
                println!("{}", e);
            })
            .unwrap();
    }
}
