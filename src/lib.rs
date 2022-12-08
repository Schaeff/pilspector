pub mod ast;
mod displayer;
mod smt;
pub mod smt_encoder;
mod validator;
mod visitor;

/// compile a file with pilcom
#[cfg(test)]
pub(crate) fn pilcom(f: &str) -> String {
    use std::{path::PathBuf, process::Command};

    let f = PathBuf::from(f);

    let dir = tempdir::TempDir::new("pil_output").unwrap();
    std::fs::create_dir_all(dir.path().join(f.clone().parent().unwrap())).unwrap();

    let out_file = dir.path().join(f.clone()).with_extension("pil.json");

    let _ = Command::new("node")
        .args([
            "pilcom/src/pil.js",
            f.as_os_str().to_str().unwrap(),
            "-o",
            out_file.as_os_str().to_str().unwrap(),
        ])
        .output()
        .expect("process failed to execute");

    std::fs::read_to_string(out_file).expect("compilation failed")
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ast::Pil;

    #[test]
    fn parse_main() {
        let pil_str = pilcom("pil/zkevm/main.pil");
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();
        pil.validate().unwrap();
    }

    #[test]
    fn display_adder() {
        let pil_str = pilcom("pil/adder.pil");
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();
        println!("{}", pil);
    }

    #[test]
    fn display_main() {
        let pil_str = pilcom("pil/zkevm/main.pil");
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();
        println!("{}", pil);
    }

    #[test]
    fn display_arrays() {
        let pil_str = pilcom("pil/arrays.pil");
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();
        assert_eq!(&pil.to_string(), "pol commit Array.x[2];\npol constant Array.y[2];\n((Array.x[0] * Array.y[1]) - (Array.x[1] * Array.y[0])) == 0\n");
    }
}
