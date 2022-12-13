# Common patterns

The patterns in this folder are present accross the zkevm PIL codebase.
Adding new files here will run them in `pilspector analyse source.pil``

## Matching rules

- Committed polynomials (`pol commit x`) are symbolic variables which can match any expression in the target PIL.
- A single polynomial identity must be provided in the pattern
- The pattern can have intermediate polynomials (`pol x = y + z`)
- Expressions can only be matched once
- Lookups, permutations, and connections are not supported
- `x` matches `expr` iff `x'` matches `expr'`, where `expr'` where `expr'` is the result of the extension of `'` to expressions: `(a + b)' == a' + b`, etc
- In particular, `x` cannot match `y'`

## Example

The following pattern:
```
namespace Pattern(%N);
    pol commit x, y, z;
    x' * y = z;
```

Would match
```
namespace SM(%N);
    pol commit a;
    pol constant b;
    (a' + b') * (a - b) = 1;
```

But not
```
namespace SM0(%N);
    pol commit a;
    pol constant b;
    // `a + b` would need to match both `x` and `y`
    // fix by changing the pattern to `x' * x = z`
    (a' + b') * (a + b) = 1; 

namespace SM1(%N);
    pol commit a;
    pol constant b;
    // `a' + b` cannot match `x'` because we can't match `x` to anything
    // fix by using more symbolic variables
    (a' + b) * (a + b) = 1;
```
