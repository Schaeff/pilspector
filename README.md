# Pilspector

## Features

- Parse PIL to Rust types
- Right now that's it

## Todo

- [x] Resolve `PolynomialId` references using `References` to get source information
- [ ] Introduce a second AST which is easier to work with?
- [x] Basic queries: number of constraints for a given variable, etc

## Caveats

- [ ] Not completely sure what the `public` operator takes as argument. Probably a `PolynomialId`
- [ ] The data structures are not 100% strict: some fields seem to only appear in the list of `Expression` (not in their children). This is not enforced by the types. I suspect it could be fixed in `serde` with flattening but I haven't found a way to make it work.
