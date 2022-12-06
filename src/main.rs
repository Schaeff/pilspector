use clap::{Parser, Subcommand};

use pilspector::analyser;
use pilspector::ast::Pil;
use pilspector::smt_encoder::SmtPil;

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
    SMT(Args),
    #[clap(about = "Apply heuristics to find underconstrained variables in PIL")]
    Analyse(Args),
}

#[derive(Debug, Clone, Parser, Default)]
pub struct Args {
    #[clap(
        long,
        short = 'i',
        value_name = "PIL_JSON",
        help = "The compiled PIL JSON"
    )]
    pub input_file: String,
}

fn main() {
    let opts = Opts::parse();
    match opts.sub {
        Subcommands::Display(args) => {
            let pil_str = std::fs::read_to_string(args.input_file).unwrap();
            let pil: Pil = serde_json::from_str(&pil_str).unwrap();
            println!("{}", pil);
        }
        Subcommands::SMT(args) => {
            let pil_str = std::fs::read_to_string(args.input_file).unwrap();
            let pil: Pil = serde_json::from_str(&pil_str).unwrap();
            let smt_pil = SmtPil::new(pil);
            println!("{}", smt_pil);
        }
        Subcommands::Analyse(args) => {
            let pil_str = std::fs::read_to_string(args.input_file).unwrap();
            let pil: Pil = serde_json::from_str(&pil_str).unwrap();
            println!();
            println!("Variables which appear the least in the state machine:");
            println!("{}", analyser::OccurrenceCounter::count(&pil));
            println!();
            println!("Occurrences of the pattern `(1 - c) * x == (1 - c) * y`:");
            println!("{}", analyser::PatternDetector::detect(&pil));
        }
    }
}
