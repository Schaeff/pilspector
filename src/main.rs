use clap::{Parser, Subcommand};

use pilspector::ast::Pil;
use pilspector::smt_encoder::{known_constants, SmtPil};

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
            let smt_pil = SmtPil::new(pil, known_constants());
            println!("{}", smt_pil);
        }
    }
}
