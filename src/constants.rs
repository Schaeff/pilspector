use std::{collections::HashMap, fs::File, io::BufReader, path::PathBuf};

use crate::ast::{
    Const, ConstantPolynomialId, FieldElement, IndexedReferenceKey, Pil, ReferenceKey,
};

#[derive(Default, Debug)]
struct Constants {
    map: HashMap<ConstantPolynomialId, Vec<FieldElement>>,
}

impl Constants {
    pub fn load(&mut self, id: &ReferenceKey, ctx: &Pil) -> std::io::Result<()> {
        let indexed_keys = ctx.get_indexed_keys(&id, ctx);
        let id = match ctx.references.get(id).unwrap() {
            crate::ast::Reference::CmP(_) => unreachable!(),
            crate::ast::Reference::ConstP(r) => r.id,
            crate::ast::Reference::ImP(_) => unreachable!(),
        };

        for key in indexed_keys {
            // small hack as files are named always like arrays, so single values have suffix 0
            let key = IndexedReferenceKey::array_element(key.key(), key.index().unwrap_or(0));

            let filename = key.to_string().replace(['.', '['], "_").replace(']', "");

            let path = PathBuf::from("./constants")
                .join(PathBuf::from(filename))
                .with_extension("json");

            println!("{}", path.display());

            let f = File::open(path)?;
            let reader = BufReader::new(f);

            let values: Vec<FieldElement> = serde_json::from_reader(reader)?;

            let id = ConstantPolynomialId(id.0 + key.index().unwrap_or(0));

            self.map.insert(id, values);
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {

    use super::*;

    #[test]
    fn load_main_constants() {
        let pil_str = std::fs::read_to_string("main.pil.json").unwrap();
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();

        let mut constants = Constants::default();

        for (key, _) in &pil.references {
            constants.load(&key, &pil).unwrap();
        }
    }
}
