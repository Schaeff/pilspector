# Pilspector

## Features

- Parse `.pil` and `.pil.json`
- Conversion to smt2, nondeterminism checks
- Pattern matching on polynomial identities

## Requirements

- rust
- nodejs
- z3

## Setup

```
git submodule update --init
cargo run
```

## Nondeterminism checks

In order to run nondeterminism checks for a state machine, Pilspector requires
the PIL source code of the state machine, the size of the execution cycle, and
what are input and output variables in the machine.

Using `byte4.pil` as an example, we have `freeIN` as the input variable, and
`out` as the output variable in the third row.

```bash
$ cargo run -- smt pil/zkevm/byte4.pil -i "Byte4_freeIN" -o "Byte4_out" -r 3

State machine is deterministic.
```
