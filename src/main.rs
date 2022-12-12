use std::collections::BTreeSet;

use clap::{Parser, Subcommand};

use pilspector::analyser;
use pilspector::load_pil;
use pilspector::smt_encoder::{known_constants, SmtPil};
use pilspector::solver;

#[derive(Debug, Parser)]
#[clap(name = "Pilspector", version = env!("CARGO_PKG_VERSION"))]
struct Opts {
    #[clap(subcommand)]
    pub sub: Subcommands,
}

#[derive(Debug, Subcommand)]
pub enum Subcommands {
    #[clap(about = "Pretty print a compiled PIL JSON.")]
    Display(Args),
    #[clap(about = "Generate a libSMT for a PIL.")]
    SMT(Args),
    #[clap(about = "Apply heuristics to find underconstrained variables in PIL")]
    Analyse(Args),
}

#[derive(Debug, Clone, Parser, Default)]
pub struct Args {
    #[clap(value_name = "PIL_FILE", help = "The PIL input file or its JSON")]
    pub input_file: String,
    #[clap(
        long,
        short = 'i',
        value_name = "INPUT_VARS",
        help = "The input variables of a state machine, separated by commas."
    )]
    pub in_vars: Option<String>,
    #[clap(
        long,
        short = 'o',
        value_name = "OUTPUT_VARS",
        help = "The output variables of a state machine, separated by commas."
    )]
    pub out_vars: Option<String>,
    #[clap(
        long,
        short = 's',
        default_value = "z3",
        value_name = "SMT_SOLVER",
        help = "The used SMT solver."
    )]
    pub solver: String,
}

fn main() {
    let opts = Opts::parse();
    match opts.sub {
        Subcommands::Display(args) => {
            println!("{}", load_pil(&args.input_file));
        }
        Subcommands::SMT(args) => {
            let pil = load_pil(&args.input_file);

            let in_vars = if let Some(vars) = args.in_vars {
                vars.split(',')
                    .map(|e| e.to_string())
                    .collect::<BTreeSet<String>>()
            } else {
                BTreeSet::default()
            };

            let out_vars = if let Some(vars) = args.out_vars {
                vars.split(',')
                    .map(|e| e.to_string())
                    .collect::<BTreeSet<String>>()
            } else {
                BTreeSet::default()
            };

            let smt_pil = SmtPil::new(pil, known_constants(), in_vars, out_vars);
            //println!("{}", smt_pil);

            let (output, error) = solver::query_smt_with_solver(
                &format!("{}", smt_pil),
                solver::SolverConfig::new(&args.solver),
            );

            if !output.is_empty() {
                println!("\nOutput = {}", output);
            }
            if !error.is_empty() {
                println!("\nError= {}", error);
            }
        }
        Subcommands::Analyse(args) => {
            let pil = load_pil(&args.input_file);

            println!();
            println!("Variables which appear the least in the state machine:");

            let occurences = analyser::OccurrenceCounter::count(&pil);
            for (pol, (itself, next)) in occurences {
                println!(
                    "{} appears {} times ({} times {} + {} times {})",
                    pol.clone(),
                    itself + next,
                    itself,
                    pol.clone().with_next(false),
                    next,
                    pol.with_next(true)
                );
            }
            println!();

            println!("Pattern detection based on `./pil/patterns`");

            for pattern_entry in std::fs::read_dir("pil/patterns").unwrap() {
                let pattern_path = pattern_entry.unwrap().path();
                if pattern_path
                    .extension()
                    .as_ref()
                    .map(|e| e.to_str().unwrap())
                    == Some("pil")
                {
                    let pattern_name = pattern_path.file_name().unwrap().to_str().unwrap();
                    let pattern = load_pil(&pattern_path.display().to_string());

                    println!(
                        "Search for the `{}` pattern in polynomial identites",
                        pattern_name
                    );
                    let occurences = analyser::PatternDetector::detect(&pil, &pattern);
                    println!("Found {} occurences:", occurences.len());
                    for (occurence, assignment) in occurences {
                        println!("Occurence:");
                        println!("{}", occurence);
                        println!();
                        println!("With assignment:");
                        println!("{}", assignment);
                        println!();
                        println!()
                    }
                    println!();
                }
            }
        }
    }
}
