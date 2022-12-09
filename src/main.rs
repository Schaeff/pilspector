use clap::{Parser, Subcommand};

use pilspector::ast::{Pil, ToStringWithContext};
use pilspector::load_pil;
use pilspector::smt_encoder::{known_constants, SmtPil};
use pilspector::{analyser, pilcom_from_str};

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
}

fn main() {
    let opts = Opts::parse();
    match opts.sub {
        Subcommands::Display(args) => {
            println!("{}", load_pil(&args.input_file));
        }
        Subcommands::SMT(args) => {
            let pil = load_pil(&args.input_file);
            let smt_pil = SmtPil::new(pil, known_constants());
            println!("{}", smt_pil);
        }
        Subcommands::Analyse(args) => {
            let pil = load_pil(&args.input_file);

            println!();
            println!("Variables which appear the least in the state machine:");
            println!("{}", analyser::OccurrenceCounter::count(&pil));
            println!();

            for pattern_entry in std::fs::read_dir("pil/patterns").unwrap() {
                let pattern_path = pattern_entry.unwrap().path();
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
