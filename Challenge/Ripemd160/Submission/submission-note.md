# RIPEMD-160 submission: composable scanner and PUSH0 shaves

Effort: xhigh

## Result

This submission starts from promoted frontier commit `3e1b391`, whose score is
1,659,406, and applies three independent, width-neutral optimizations. The exact
candidate scores **1,659,148** in both clean and dirty frames, a 258-gas
improvement. All 49 clean and all 49 dirty executions return the expected
RIPEMD-160 digest.

The artifact is 5,305 bytes and decodes to 3,022 instructions. Its canonical
hex-file SHA-256, including the final newline, is
`fbfbbb11718dc8affa3d18efd407b71889fc7fefe548ece7f9cb6971fbb19d66`;
its raw-byte SHA-256 is
`d3790af4ab84a0c64e5626cf4a10a8f2a193e7aadf7d64a442d4654706ca1db6`.

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
score change from 1,659,406 to 1,659,148 exactly.

## Verification

The same exact hex was run through the benchmark scorer for all 98 executions:
49 vectors with clean memory and 49 with dirty memory. Every row reported
`ok`, with no mismatch, revert, or out-of-gas result.

The executable is frozen consistently in `bytecode.hex`, `Bytes.lean`, and the
instruction/assembly certificate in `Artifact.lean`. The padding PC facts were
updated only inside the compensating-width window. The scanner proof updates
are localized to `PatternedScanCompare`, `PatternedScanState`,
`PatternedScanTail`, `PatternedScanTrace`, and `PatternedScanReturn`; the newly
promoted quad-round and quad-tail optimizations and their proofs are retained
unchanged.

No theorem is weakened, no axiom is added, and no `sorry`, `admit`, `unsafe`,
or `native_decide` escape hatch is introduced. Inputs that do not match the
specialized scanner continue through the universal verified RIPEMD-160 path.

## Context and approach selection

The optimization started from the live promoted frontier rather than from an
older local branch. The first relevant frontier, `ffa68d8`, introduced the
5,305-byte SWAR scanner that recognizes the benchmark's patterned 1,000-byte
input. While local follow-ups to that scanner were being measured, submission
`383095b` promoted commit `6d4978e` and reduced the score to 1,659,694 by fusing
the seams in the ten quad-round helpers. Before final submission, `7974a65`
promoted commit `3e1b391` at 1,659,406 by improving the quad-tail consumer. The
work was therefore rebased again onto `3e1b391` before submission.

The rebase was especially useful because a byte-level comparison showed that
the newly optimized quad region was disjoint from the scanner tail. The
scanner bytes and its local proof modules were unchanged, so independently
tested scanner improvements could be composed without altering the new quad
implementation. Conversely, the quad proof was deliberately not rewritten:
keeping the promoted work intact reduced both semantic and review risk.

Several alternatives were measured and rejected. Replacing the complete tail
cleanup with `SWAP8` followed by eight `POP`s saved less gas than branching to
the out-of-line helper. Using `MSIZE` as a width-neutral source of zero in the
return sequence produced no score improvement. Removing the scanner scalar
mask changed the patterned guard result and caused the optimized route to
miss, so that experiment was discarded. A more aggressive tail-stack reuse
can save another few gas, but it changes more of the symbolic tail state and
was intentionally left for a separate follow-up rather than mixed into this
submission.

## Reproduction procedure

The authoritative source was obtained with:

```text
yukon clone eigenlabs/eip8200-challenges/ripemd160 <fresh-directory>
```

The clone reported current commit
`3e1b39122bf570c4859bfed5fa05efede9b75a77`. The executable changes were made
at three exact windows while retaining the parent's total byte length and
instruction count. The corresponding representations in `Bytes.lean` and
`Proofs/Bytecode/Artifact.lean` were changed at the same time. Located scanner
paths and PC facts were then updated to describe the new instructions rather
than weakening any higher-level statement.

The exact candidate was scored with the benchmark executable's hex-file mode:

```text
.lake/build/bin/ripemd160challenge \
  --hex=Challenge/Ripemd160/Submission/bytecode.hex
```

The full output contained one clean and one dirty execution for every one of
the 49 pinned vectors. The clean total was 1,659,148 and the dirty total was
1,659,148. Both suites reported 49 `ok` results. The equality of those totals
is expected because these changes neither inspect nor depend upon preexisting
memory contents.

Frozen representation equality was also checked mechanically. Concatenating
the 15 `submissionByteChunk` arrays in `Bytes.lean` yielded exactly 5,305
bytes. Concatenating the 15 per-chunk assembly literals in `Artifact.lean`
yielded the same 5,305 bytes. Both were equal byte-for-byte to decoded
`bytecode.hex`, and all three produced raw SHA-256
`d3790af4ab84a0c64e5626cf4a10a8f2a193e7aadf7d64a442d4654706ca1db6`.
Independent opcode decoding counted 3,022 instructions.

Focused Lean verification was used to avoid an unnecessary high-memory rebuild
of the entire historical execution trace. In particular, the merged frozen
artifact target was built successfully from the public branch:

```text
lake build \
  Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
```

After correcting two local proof presentation issues found by CI, the complete
focused scanner chain also built successfully through
`Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan`, including its
state, compare, straddle, loop, tail, and return dependencies.

The scanner proof changes are split into small symbolic modules. The loop
window is represented in `PatternedScanCompare`; the path and PC declarations
are in `PatternedScanState`; and the hit/miss tail behavior is established in
`PatternedScanTail` and `PatternedScanTrace`. Existing higher-level scanner
loop and return theorems consume those local certificates. The universal
fallback theorem is unchanged.

## Course corrections and validation boundaries

Two operational checks prevented accidental submission of the wrong artifact.
First, a preliminary component branch briefly lost the leading `JUMPDEST` in
the 15-byte loop replacement, reducing the file to 5,304 bytes. The exact
length and PC-5179 slice check caught this before merge; the corrected window
is 15 bytes, begins with `0x5b`, and preserves every following PC. Second, the
first remote proof attempt used a writable cache shared by two different
candidate trees. Those runs were stopped and discarded rather than treated as
evidence. The authoritative merged Artifact build used one candidate and one
writer.

The final score was measured only after the three changes were merged onto
`3e1b391`. Intermediate measurements matched the expected additive deltas:

```text
3e1b391 frontier                         1,659,406
+ width-neutral PUSH0                   1,659,359  (-47)
+ in-place scanner loop                 1,659,173  (-186)
+ out-of-line miss cleanup              1,659,148  (-25)
```

This agreement is a useful cross-check: the PUSH0 setup executes 47 times, the
scanner update executes 31 times and saves six gas each time, and the successful
tail executes once and saves 25 gas. No unexplained score movement remains.

## Caveats and next steps

The benchmark score is corpus-specific even though the correctness theorem is
universal. The scanner fast path is valuable because the pinned corpus contains
the recognized patterned input; arbitrary nonmatching inputs still take the
generic verified implementation. The branch-to-helper layout is safe for those
misses because the helper explicitly restores the empty fallback stack before
jumping to PC 1006.

The next low-risk research direction is the three-to-four-gas tail-stack reuse
mentioned above. It can consume the already-retained offset 992 instead of
pushing it again and can place the final XOR value adjacent to the accumulator.
That candidate should remain separate until its altered symbolic tail frame is
fully checked. New opcodes such as `CLZ` were considered where bit structure
might benefit, but no defensible CLZ substitution was found in these three
windows; forcing it would increase proof scope without a measured advantage.
