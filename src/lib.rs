pub mod analyser;
use ast::Pil;
pub mod ast;
// mod constants;
mod displayer;
mod folder;
mod smt;
pub mod smt_encoder;
pub mod solver;
mod validator;
mod visitor;

/// compile a string with pilcom
pub fn pilcom_from_str(source: &str) -> Result<String, String> {
    use std::process::Command;

    let dir = tempdir::TempDir::new("pil_input").unwrap();
    let f = dir.path().join("input.pil");
    std::fs::write(f.clone(), source).unwrap();

    let dir = tempdir::TempDir::new("pil_output").unwrap();
    std::fs::create_dir_all(dir.path().join(f.parent().unwrap())).unwrap();

    let out_file = dir.path().join(f.clone()).with_extension("pil.json");

    let res = Command::new("node")
        .args([
            "pilcom/src/pil.js",
            f.as_os_str().to_str().unwrap(),
            "-o",
            out_file.as_os_str().to_str().unwrap(),
        ])
        .output()
        .map_err(|err| format!("Could not run pilcom: {}", err))?;

    if !res.status.success() {
        return Err(String::from_utf8(res.stdout).unwrap());
    }

    Ok(std::fs::read_to_string(out_file).unwrap())
}

/// compile a file with pilcom
pub fn pilcom(f: &str) -> Result<String, String> {
    use std::{path::PathBuf, process::Command};

    let f = PathBuf::from(f);

    let dir = tempdir::TempDir::new("pil_output").unwrap();
    std::fs::create_dir_all(dir.path().join(f.parent().unwrap())).unwrap();

    let out_file = dir.path().join(f.clone()).with_extension("pil.json");

    Command::new("node")
        .args([
            "pilcom/src/pil.js",
            f.as_os_str().to_str().unwrap(),
            "-o",
            out_file.as_os_str().to_str().unwrap(),
        ])
        .output()
        .map_err(|err| format!("Could not run pilcom: {}", err))?;

    std::fs::read_to_string(out_file).map_err(|_| "pilcom compilation failed".into())
}

/// Attempt to load either PIL JSON description, or the PIL file transparently.
pub fn load_pil(filename: &str) -> Pil {
    // First try to parse as a JSON
    let json_str = std::fs::read_to_string(filename).unwrap();
    serde_json::from_str(&json_str)
        .or_else(|json_err| -> Result<Pil, (_, String)> {
            // Parsing as JSON failed, parse as PIL
            let json_str = pilcom(filename).map_err(
                // Both parsings failed, return both errors
                |pil_err| (json_err, pil_err),
            )?;
            // This time should not fail
            Ok(serde_json::from_str(&json_str).unwrap())
        })
        .unwrap()
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ast::Pil;

    #[test]
    fn parse_main() {
        let pil_str = pilcom("pil/zkevm/main.pil").unwrap();
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();
        pil.validate().unwrap();
    }

    #[test]
    fn display_adder() {
        let pil_str = pilcom("pil/adder.pil").unwrap();
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();
        println!("{}", pil);
    }

    #[test]
    fn display_main() {
        let pil_str = pilcom("pil/zkevm/main.pil").unwrap();
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();
        println!("{}", pil);
    }

    #[test]
    fn display_arrays() {
        let pil_str = pilcom("pil/arrays.pil").unwrap();
        let pil: Pil = serde_json::from_str(&pil_str).unwrap();
        assert_eq!(&pil.to_string(), "pol commit Array.x[2];\npol constant Array.y[2];\n((Array.x[0] * Array.y[1]) - (Array.x[1] * Array.y[0])) == 0\n");
    }
}
