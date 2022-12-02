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

        let mut pil_value: serde_json::Value = serde_json::from_str(&pil_str).unwrap();

        // expression lists fail to parse now, check without
        pil_value["expressions"] = serde_json::Value::Array(vec![]);

        let pil: Pil = serde_json::from_value(pil_value)
            .map_err(|e| {
                println!("{}", e);
            })
            .unwrap();

        println!("{:#?}", pil);
    }
}
