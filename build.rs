use std::process::Command;

fn main() {
    // init submodules
    let _ = Command::new("git")
        .args(["submodule", "init"])
        .output()
        .expect("process failed to execute");

    // update submodules
    let _ = Command::new("git")
        .args(["submodule", "update"])
        .output()
        .expect("process failed to execute");

    // install pilcom
    let _ = Command::new("npm")
        .args(["install", "--prefix", "./pilcom"])
        .output()
        .expect("process failed to execute");
}
