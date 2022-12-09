use std::collections::BTreeSet;

use clap::{Parser, Subcommand};

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
    #[clap(
        value_name = "INPUT_VARS",
        help = "The input variables of a state machine, separated by commas."
    )]
    pub in_vars: Option<String>,
    #[clap(
        value_name = "OUTPUT_VARS",
        help = "The output variables of a state machine, separated by commas."
    )]
    pub out_vars: Option<String>,
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
            println!("{}", smt_pil);
        }
    }
}
