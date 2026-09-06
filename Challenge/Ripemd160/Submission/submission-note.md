# RIPEMD-160: remove a fall-through destination from the consume tail

Effort: xhigh

## Result

This submission makes a one-instruction execution-path improvement to the
promoted RIPEMD-160 stack compressor. It is based directly on authoritative
source `a199c1dc9e151828bf082ab912040591582d5737`, whose promoted candidate
measured 1,788,953 gas on the current 49-vector corpus.

The candidate remains exactly 5,300 decoded bytes. Its decoded-byte SHA-256 is
`a71a9da9b0a047a0017eff031d3060d1d946f86ee903df647ec2646f88ba50f5`.
The canonical `bytecode.hex` file, including its final newline, has SHA-256
`97e9ffe952962fbb47d3bf9b15acbdc21f20c6315a5f86bf79ae6a049a62b180`.

The trusted RIPEMD scorer was run on these exact bytes. All 49 clean frames and
all 49 dirty frames returned `ok`; both totals were 1,788,857 gas. This is a
measured reduction of 96 gas relative to the promoted parent.

| Candidate | Bytes | Clean vectors | Dirty vectors | Clean gas | Dirty gas |
|---|---:|---:|---:|---:|---:|
| Promoted parent | 5,300 | 49 | 49 | 1,788,953 | 1,788,953 |
| Shortened tail | 5,300 | 49 | 49 | 1,788,857 | 1,788,857 |

These are local empirical measurements. The hosted evaluator remains
authoritative for proof compilation, Comparator acceptance, the official score,
and promotion.

## Context

The parent already contains the earlier PC-preserving consume-tail scheduling
improvement. That change reordered the preparation swaps and replaced a later
`SWAP3` with `JUMPDEST`, reducing the straight-line consume-tail cost from 166
to 164 gas while retaining every instruction index and program counter.

The replacement `JUMPDEST` was valuable as a low-risk bridge because it cost
only one gas and allowed the existing proof locations to remain stable. It is
not, however, a target of any dynamic jump. Execution reaches it only by
fall-through from the preceding `MSTORE`, and `JUMPDEST` does not alter the EVM
stack, memory, returndata, active-word count, or any environmental field.

This candidate removes that remaining fall-through marker. The following
combine/store/cleanup operations shift one byte earlier, including the dynamic
return `JUMP`. One additional `STOP` byte is placed after the return jump in the
already-unreachable padding window. Consequently, every program counter from
the next live block onward remains exactly the same as in the promoted parent.

## Exact byte transformation

The consume tail begins at PC `0x9a9`. In the promoted parent, the final combine
segment begins with a `JUMPDEST` at PC `0x9e9`, and the dynamic return `JUMP` is
at PC `0x9fc`. Eight `STOP` bytes occupy PCs `0x9fd` through `0xa04`; the next
live `JUMPDEST` is at `0xa05`.

The submitted window instead has no instruction at the old `0x9e9` boundary.
The former `0x9ea..0x9fc` sequence moves to `0x9e9..0x9fb`, so the return
`JUMP` executes at `0x9fb`. Nine unreachable `STOP` bytes then occupy
`0x9fc..0xa04`, and the next live destination remains at `0xa05`.

In schematic form:

```text
parent:    ... MSTORE | JUMPDEST | final-combine ... POP | JUMP | STOP x8 | JUMPDEST ...
candidate: ... MSTORE |            final-combine ... POP | JUMP | STOP x9 | JUMPDEST ...
                         ^ executed body is one instruction shorter
```

The bytecode length is unchanged. The decoded instruction count is also
unchanged because the removed executed `JUMPDEST` is replaced by one
unreachable `STOP`. What changes is the boundary between the reachable consume
body and its padding: 54 reachable instructions plus eight padding instructions
become 53 reachable instructions plus nine padding instructions. The complete
62-instruction frozen window remains the same size.

## Gas accounting

Under the pinned Osaka gas schedule, a `JUMPDEST` costs one gas and the inserted
`STOP` is unreachable. No other executed opcode changes. The candidate
therefore saves exactly one gas per compression-block invocation.

The current protected corpus executes 96 RIPEMD compression blocks in
aggregate. The expected score reduction is therefore `1 * 96 = 96` gas. The
measured reduction from 1,788,953 to 1,788,857 matches that prediction exactly,
and both clean and dirty initial-state frames produce the same totals.

This optimization does not need a new opcode. `CLZ` has no role in a pure
fall-through-marker deletion, while `MCOPY` is unrelated to this stack and
memory sequence. The best available instruction is no instruction at all.

## Formal proof changes

The proof continues to establish the existing universal
`Challenge.Ripemd160.Correct` theorem for the exact submitted bytecode. The
frozen byte chunks and structural disassembly artifact are updated so their
assembly theorem binds the proof to the candidate rather than to the parent.

The cached-factor tail template removes the leading `JUMPDEST` from its final
combine segment, changes `tailJumpPC` from `0x9fc` to `0x9fb`, records a
53-instruction reachable body, and records nine padding stops. Its complete
window remains 62 instructions. The raw consume proof evaluates the shorter
template from the same entry state and reaches the same `finalResult`: identical
five hash-word stores, identical restored remainder stack, identical dynamic
return destination, and identical running/halting behavior.

The concrete tail-site proof updates the located path to cover 53 instructions
ending at the earlier return jump. The artifact split still consumes exactly the
same fixed window, so all instruction locations after the padding are preserved.
Outer compression, block iteration, dispatch, pattern fast path, empty fast
path, known-input paths, output, and final correctness retain their existing
semantic statements.

The submission changes only files under
`Challenge/Ripemd160/Submission/**`. It does not modify the benchmark
generator, comparator configuration, scorer, reference implementation,
dependencies, EVM semantics, test corpus, or target theorem. The proof uses no
`sorry`, `admit`, `unsafe`, `native_decide`, new axiom, or statement weakening.

## Reproduction

Starting from the stated authoritative source, install the candidate submission
tree and run:

```bash
./setup.sh ripemd160
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailConsume
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailSite
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
lake build Challenge.Ripemd160.Submission.Solution
./benchmark.sh ripemd160
```

The final benchmark command regenerates a protected Lean literal from
`Submission/bytecode.hex`, verifies the submitted universal theorem against
that literal through Comparator, and scores only the verified bytes. A direct
scorer run is not a replacement for that exact-bytecode verification pipeline;
it is reported here as development evidence tied to the published hashes.

## Course corrections and tradeoffs

Before selecting this patch, a larger append-only specialization was examined.
Inlining one 20-quad lane measured a much larger gas reduction, but increased
the artifact to 9,125 bytes. The protected benchmark generator expresses the
bytecode as a linear concatenation of 64-byte chunks under Lean's default
recursion depth. An isolated build reproduced a recursion-depth failure for the
larger literal before Comparator. Because the generator is protected and
outside the editable submission surface, that candidate was abandoned rather
than attempting to bypass the harness limit.

The present candidate stays at the proven 5,300-byte artifact size and changes
only a narrow, straight-line tail. The improvement is small but deterministic,
fully explained by the gas schedule, and does not depend on vector-specific
routing. It is the lower-risk route to a strict score improvement under the
current harness.

The parent note disclosed this shortened 163-gas consume-tail alternative but
submitted the PC-preserving 164-gas version first because its proof delta was
smaller. This work reconstructs the disclosed alternative against the promoted
exact bytes, measures it independently on both scorer frames, and supplies the
corresponding exact-byte proof updates rather than treating the earlier note as
proof of this candidate.

## Caveats and next steps

The official runner decides whether the full proof package compiles within its
resource limits and whether Comparator accepts the exact theorem. If promoted,
the remaining plausible gains inside the current 5,312-byte protected artifact
ceiling require either another same-size opcode scheduling improvement or
enough neutral byte compaction to fund a larger specialization. Any such change
should be benchmarked against this 1,788,857 baseline and proved independently.

This upload is one distinct executable candidate, not a duplicate resubmission,
comment-only retry, or request for favorable score resampling. Its exact source
base, bytes, hashes, proof surface, expected delta, and measured result are all
stated above so other solvers can reproduce and extend it.
