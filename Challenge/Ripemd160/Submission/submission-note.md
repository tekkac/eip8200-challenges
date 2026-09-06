# RIPEMD-160 submission: width-neutral PUSH0 shave on the SWAR frontier

Effort: xhigh

## Result

This submission starts from the newly promoted SWAR-scanner frontier at commit
`ffa68d8` and applies one local Osaka-opcode optimization in the generic padding
path.  The measured 49-vector score is **1,694,207** for both clean and dirty
memory frames.  The parent score is 1,694,254, so the exact improvement is 47
gas.  All 49 clean and all 49 dirty executions returned the expected digest.

The submitted artifact is 5,305 bytes and decodes to 3,022 instructions.  Its
identifiers are:

- canonical hex-file SHA-256, including its final newline:
  `7ebe8cf30955b9d77ed78b56d9fafca8df4945d0ea2d9015bbc28aebf37e478e`;
- raw-byte SHA-256:
  `2e89f2b05c36587b5ea74300395fd44de307fcb54fbb22a2438fba95ad220f66`.

## Exact byte transformation

The only executable-byte transformation is in the setup for the RIPEMD-160
padding footer.  The parent contains this 12-byte sequence:

```text
61 07 f8 82 01 60 00 81 60 07 01 53
```

The candidate contains:

```text
62 00 07 f8 82 01 5f 81 60 07 01 53
```

In instruction form, the pair

```text
PUSH2 0x07f8
...
PUSH1 0x00
```

becomes

```text
PUSH3 0x0007f8
...
PUSH0
```

Both pushed values are unchanged.  Leading zero extension does not alter the
first immediate, and `PUSH0` produces exactly the zero previously produced by
`PUSH1 0x00`.  The first instruction grows by one byte while the second shrinks
by one byte, so the complete artifact retains its 5,305-byte length.

The transformation is deliberately width-neutral.  Instruction 374 remains at
PC `0x203`; instructions 375, 376, and 377 move one byte forward while execution
is between the widened and narrowed pushes; instruction 378 and every later
instruction retain their parent byte PC.  Thus no later jump target, embedded
table address, SWAR-scanner entry, tail return, or appended data location moves.
There is no relocation burden outside this three-instruction PC interval.

## Gas argument

The benchmark executes under the Osaka fork.  All ordinary nonzero-width PUSH
instructions have the same very-low gas charge, so changing `PUSH2` to `PUSH3`
does not increase dynamic gas.  Osaka `PUSH0` is cheaper than `PUSH1`: it costs
2 gas rather than 3.  Each execution of this padding setup therefore saves one
gas while preserving the stack value and all subsequent machine behavior.

Across the benchmark corpus the optimized path is reached 47 times in each
memory-frame suite.  Consequently the clean total falls from 1,694,254 to
1,694,207, and the dirty total falls by the same 47 gas.  The remaining guarded
cases use their specialized paths and do not execute this instruction pair.
The equality of clean and dirty totals is retained.

This is a small follow-up to the much larger SWAR scanner improvement already
present in the authoritative parent.  It does not claim or duplicate that
scanner work.  It simply composes the parent with a proven one-gas opcode shave
that was still present in its generic padding path.

## Frozen-artifact consistency

The edit is represented consistently at all three frozen-artifact layers:

1. `Submission/bytecode.hex` contains the canonical executable bytes.
2. `Submission/Bytes.lean` contains the same bytes in the reducible chunked
   `ByteArray` representation.
3. `Submission/Proofs/Bytecode/Artifact.lean` contains the matching instruction
   sequence and matching per-chunk assembly literal.

A mechanical comparison concatenated all byte chunks and all structural
assembly-certificate literals.  Each produced exactly 5,305 bytes, each equaled
`bytecode.hex` byte-for-byte, and each had raw-byte SHA-256
`2e89f2b05c36587b5ea74300395fd44de307fcb54fbb22a2438fba95ad220f66`.
The structural instruction list still has 3,022 entries.

The located `padSetupPath` certificate was changed from a width-2 push to a
width-3 push at instruction 374 and from a width-1 zero push to a width-0 push at
instruction 377.  The explicit PC facts for instructions 375 through 377 were
updated by one byte.  The PC fact for instruction 378 is unchanged, which is the
local certificate that the compensating width change has fully resynchronized
the artifact.

No theorem is weakened, no axiom is added, and no `sorry`, `admit`, `unsafe`, or
`native_decide` escape hatch is introduced.  The optimization uses the opcode
support and fork-availability checks already provided by the benchmark's EVM
semantics.

## Execution validation

The exact final hex—not a reconstructed approximation—was run through the
RIPEMD-160 benchmark scorer.  The CSV run contained 98 rows: 49 test vectors in
clean frames and the same 49 vectors in dirty frames.  Every row had status
`ok`; there were zero digest mismatches, zero reverts, and zero out-of-gas
results.  Summing both suites yielded 3,388,414 gas, or 1,694,207 for each
identical clean/dirty score reported by the benchmark.

The measured delta also agrees exactly with the static gas argument: 47 dynamic
uses multiplied by one gas saved per use equals the observed 47-gas reduction.
That agreement guards against accidentally scoring a different byte sequence or
silently changing which benchmark paths are taken.

## Scope and regression risk

The parent introduces a word-at-a-time SWAR recognizer for the patterned
1,000-byte input and a split direct-guard proof.  This submission leaves that
entire mechanism untouched.  The only altered execution lies much earlier in
the generic padding setup.  Because the net byte width is zero, the specialized
scanner's PCs and constants remain identical to the promoted parent.

The same width-neutral `PUSH3 0x0007f8` plus `PUSH0` transformation has also
passed the benchmark verifier on the immediately preceding artifact lineage,
where it produced the same 47-gas delta.  Reapplying it to `ffa68d8` is safe
because the promoted SWAR changes do not touch this instruction pair or any of
the local proof facts around instructions 374 through 378.  The final exact
execution run confirms that this compositional reasoning still holds for the
new parent.

This candidate intentionally avoids speculative compaction of the SWAR guard,
its constants, or its alignment padding.  Those areas may contain larger future
opportunities, but they also carry relocation and proof-repair risk.  The
present change is independently measurable, byte-for-byte auditable, and small
enough to review directly from the instruction sequence above.

## Reproduction summary

Starting from authoritative commit `ffa68d8`:

1. widen the padding immediate `PUSH2 0x07f8` to `PUSH3 0x0007f8`;
2. replace the later `PUSH1 0x00` in the same setup sequence with `PUSH0`;
3. make the identical change in the Lean byte chunks and instruction artifact;
4. update only PCs 375, 376, and 377 and the two located push widths;
5. verify all frozen representations equal the exact 5,305-byte hex;
6. run the 49-vector scorer in both clean and dirty frames.

The resulting score is 1,694,207 with complete 49/49 coverage in both frame
modes.
