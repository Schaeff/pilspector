use std::collections::BTreeMap;
use std::io::Write;
use std::process::Command;
use std::str::FromStr;
use tempfile::NamedTempFile;

use crate::sexpr::SExpr;

pub fn query_smt_with_solver(query: &String, solver: SolverConfig) -> (String, String) {
    let (output, error) = query_smt_internal(&format!("{query}\n(check-sat)\n(get-model)"), solver);

    if !output.starts_with("sat") && !output.starts_with("unsat") {
        panic!(
            "Invalid output from smt solver.\nQuery: {query}\nStdout: {output}\nStderr: {error}",
        );
    }

    (output, error)
}

pub fn query_smt_with_solver_return_model(
    query: &String,
    solver: SolverConfig,
) -> (bool, BTreeMap<String, String>) {
    let (output, error) = query_smt_with_solver(query, solver);
    assert_eq!(error, "");
    if output.starts_with("sat") {
        let lines = output
            .split('\n')
            .map(|s| s.trim())
            .filter(|s| !s.is_empty())
            .collect::<Vec<_>>();

        (
            true,
            SExpr::from_str(lines[1..].join(" ").trim().to_string().as_str())
                .unwrap()
                .as_subexpr()
                .iter()
                .filter_map(|e| {
                    let items = e.as_subexpr();
                    match &items[..] {
                        [SExpr::Symbol(cmd), SExpr::Symbol(fun_name), _, _, value]
                            if cmd.as_str() == "define-fun" =>
                        {
                            Some((fun_name.clone(), value.to_string()))
                        }
                        _ => None,
                    }
                })
                .collect::<BTreeMap<String, String>>(),
        )
    } else {
        (false, Default::default())
    }
}

fn query_smt_internal(query: &String, solver: SolverConfig) -> (String, String) {
    let mut file = NamedTempFile::new().unwrap();
    file.write_all(query.as_bytes()).unwrap();

    let output = Command::new(solver.cmd)
        .args(solver.args)
        .args([file.path()])
        .output()
        .expect("failed to run query");

    match (
        String::from_utf8(output.stdout),
        String::from_utf8(output.stderr),
    ) {
        (Ok(output), Ok(stderr)) => (output, stderr),
        (Err(err), _) | (_, Err(err)) => {
            panic!("Could not decode output from SMT solver.\nError: {}", err)
        }
    }
}

#[derive(Clone)]
pub struct SolverConfig {
    cmd: String,
    args: Vec<String>,
}

pub enum SMTSolver {
    Z3,
    CVC4,
    CVC5,
}

impl SolverConfig {
    pub fn new(cmd: &str) -> Self {
        match SMTSolver::from_str(cmd) {
            Ok(SMTSolver::Z3) => SolverConfig {
                cmd: cmd.into(),
                args: vec![],
            },
            Ok(SMTSolver::CVC4) => SolverConfig {
                cmd: cmd.into(),
                args: vec!["--lang".into(), "smt2".into(), "--produce-models".into()],
            },
            Ok(SMTSolver::CVC5) => SolverConfig {
                cmd: cmd.into(),
                args: vec!["--lang".into(), "smt2".into(), "--produce-models".into()],
            },
            _ => panic!(),
        }
    }
}

impl FromStr for SMTSolver {
    type Err = ();
    fn from_str(solver: &str) -> Result<SMTSolver, Self::Err> {
        match solver {
            "z3" => Ok(SMTSolver::Z3),
            "cvc4" => Ok(SMTSolver::CVC4),
            "cvc5" => Ok(SMTSolver::CVC5),
            _ => Err(()),
        }
    }
}
