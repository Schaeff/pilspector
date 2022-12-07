use std::path::PathBuf;
use walkdir::WalkDir;

fn main() {
    // compile all pil files
    use std::process::Command;

    use std::env;

    for entry in WalkDir::new("pil") {
        let entry = entry.unwrap();

        if entry.file_type().is_dir() {
            let _ =
                std::fs::create_dir(PathBuf::from(env::var("OUT_DIR").unwrap()).join(entry.path()));
        } else if entry.file_type().is_file() {
            let out_file = PathBuf::from(env::var("OUT_DIR").unwrap())
                .join(entry.path())
                .with_extension("pil.json");

            let out = Command::new("node")
                .args([
                    "pilcom/src/pil.js",
                    entry.path().as_os_str().to_str().unwrap(),
                    "-o",
                    out_file.as_os_str().to_str().unwrap(),
                ])
                .output()
                .expect("process failed to execute");

            println!("{:?}", out);
        }
    }
}
