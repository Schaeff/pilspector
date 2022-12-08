use clap::{Parser, Subcommand};

use pilspector::ast::Pil;
use pilspector::load_pil;
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
    #[clap(about = "Generate a libSMT for a PIL.")]
    SMT(Args),
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
    }
}
