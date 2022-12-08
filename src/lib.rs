pub mod ast;
mod displayer;
mod smt;
pub mod smt_encoder;
mod validator;
mod visitor;

/// get the path for a compiled PIL file
#[cfg(test)]
pub(crate) fn pil_json(f: &str) -> String {
    use std::{path::PathBuf, process::Command};

    let f = PathBuf::from("pil").join(PathBuf::from(f));

    let dir = tempdir::TempDir::new("pil_output").unwrap();
    std::fs::create_dir_all(dir.path().join(f.clone().parent().unwrap())).unwrap();

    let out_file = dir.path().join(f.clone()).with_extension("pil.json");

    let out = Command::new("node")
        .args([
            "pilcom/src/pil.js",
            f.as_os_str().to_str().unwrap(),
            "-o",
            out_file.as_os_str().to_str().unwrap(),
        ])
        .output()
        .expect("process failed to execute");

    println!("{:?}", out);

    std::fs::read_to_string(out_file).unwrap()
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ast::Pil;

    #[test]
    fn parse_main() {
        let pil_str = pil_json("zkevm/main.pil");
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();
        pil.validate().unwrap();
    }

    #[test]
    fn display_adder() {
        let pil_str = pil_json("adder.pil");
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();
        println!("{}", pil);
    }

    #[test]
    fn display_main() {
        let pil_str = pil_json("zkevm/main.pil");
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();
        println!("{}", pil);
    }
}
