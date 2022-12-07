# extract_constants

A script to extract the constant columns.

Notes:
- The result gets written into `../constants`
- N is set to 2^21 (vs 2^23 in production). This is not expected to be an issue for the smaller state machines as N is driven by the number of steps in the main state machine.
- the Rom and Storage state machines are ignored

## Usage

```
npm i
npm run extract
```