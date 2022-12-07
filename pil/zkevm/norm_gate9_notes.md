# norm_gate9

- Part of keccak, not on audit scope

## constants:
- Value3, Value3Norm: some table, to normalize some values
- Gate9Type, Gate9A, Gate9B, Gate9C: some table with 2 different gates, 2 in 1 out
- latch: some clock. somehow starts with 0, the 001 repeated
- factor: some shifting by `(2**21)**(0, 1, 2)`

## committed
freeA, freeB: unnormed
gateType must stay constant during a period
gateType must be 1 or 0, enforced by the lookup

freeANorm, freeBNorm, freeCNorm: probably normed

make sure freeANorm is the norm of freeA
make sure freeBNorm is the norm of freeB

call the Gate. It expects normed inputs and forces gateType to 0/1

construct the output with latch

there are no tests for it


# how it works
build a value which can be retrieved when Latch is 1.