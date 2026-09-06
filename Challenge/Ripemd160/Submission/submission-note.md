# RIPEMD-160 submission: composable scanner and PUSH0 shaves

Effort: xhigh

## Result

This submission starts from promoted frontier commit `6d4978e`, whose score is
1,659,694, and applies three independent, width-neutral optimizations. The exact
candidate scores **1,659,436** in both clean and dirty frames, a 258-gas
improvement. All 49 clean and all 49 dirty executions return the expected
RIPEMD-160 digest.

The artifact is 5,305 bytes and decodes to 3,022 instructions. Its canonical
hex-file SHA-256, including the final newline, is
`9953bf54aa477c98e81ca2b43b183acf3b8d0f51f10ed1637d8681e2d00d2f77`;
its raw-byte SHA-256 is
`edf96b5a9df16451cb7b15dc98ddd5b3a2f3aa4dfae1278de72b547fa916feed`.

## Changes

First, the generic padding setup widens `PUSH2 0x07f8` to
`PUSH3 0x0007f8` and replaces the nearby `PUSH1 0` with Osaka `PUSH0`.
The values, net width, instruction count, and every PC from the next
instruction onward are unchanged. `PUSH0` saves one gas on each of the 47
corpus executions that reach this setup, for 47 gas total.

Second, the 31-iteration patterned-input scanner updates its scalar and offset
in place. Redundant duplication followed by shuffle-and-pop replacement is
removed; width- and index-neutral `JUMPDEST` instructions occupy the alignment
slots. The exact 15-byte loop window changes from

```text
80 60a0 01 60ff 16 90 50 81 6020 01 91 50
```

to

```text
5b 60a0 01 60ff 16 5b 5b 90 6020 01 90 5b
```

This saves six gas per iteration, or 186 gas on the patterned vector, while
preserving the loop boundary state and all later PCs and instruction indices.

Third, successful scanner hits no longer execute the miss-only stack cleanup.
The tail branches to a helper placed in previously unreachable guard filler
when the accumulated mismatch is nonzero. The helper pops the eight retained
scanner words and rejoins the universal implementation at PC 1006. A zero
mismatch falls through directly to the existing digest return. Rebalanced
unreachable padding preserves the 5,305-byte artifact, the 3,022-instruction
count, and all PCs and instruction indices after the tail region. This saves 25
gas on the patterned hit; misses retain the fully verified universal fallback.

The measured reduction is therefore `47 + 186 + 25 = 258` gas, matching the
score change from 1,659,694 to 1,659,436 exactly.

## Verification

The same exact hex was run through the benchmark scorer for all 98 executions:
49 vectors with clean memory and 49 with dirty memory. Every row reported
`ok`, with no mismatch, revert, or out-of-gas result.

The executable is frozen consistently in `bytecode.hex`, `Bytes.lean`, and the
instruction/assembly certificate in `Artifact.lean`. The padding PC facts were
updated only inside the compensating-width window. The scanner proof updates
are localized to `PatternedScanCompare`, `PatternedScanState`,
`PatternedScanTail`, and `PatternedScanTrace`; the newly promoted quad-round
optimization and its proofs are retained unchanged.

No theorem is weakened, no axiom is added, and no `sorry`, `admit`, `unsafe`,
or `native_decide` escape hatch is introduced. Inputs that do not match the
specialized scanner continue through the universal verified RIPEMD-160 path.
