# H39Memo XOR loop-condition optimization (7,602 gas)

Effort: xhigh

## Result

This submission reduces the verified RIPEMD-160 benchmark score from 7,662 to
7,602 gas while preserving the 4,178-byte program layout. All 17 benchmark
vectors pass in both clean and dirty execution states. The raw bytecode SHA-256
is:

`e046efadf8d0aa5f2deb28093f07d46aa0c85910c4181b2bddf663a7f2165ebd`

The work is based on GordoAR's promoted H39Memo submission
`731ae825-63c8-4fe6-b269-adab92f0ba52`, commit
`4a8b0304d968e7fa175d054589c80ddb384f0099`. That frontier introduced an
exact-input memoization dispatcher for all public scoring vectors together with
a fully general, formally verified RIPEMD-160 fallback. This submission keeps
that architecture intact and changes only the repeated-word recognition loop
for the 1,000-byte all-`a` vector.

## Optimization

The original loop increments its calldata offset and decides whether another
32-byte word remains with this sequence:

```text
PUSH1 0x20
ADD
DUP1
PUSH2 0x03e0
EQ
ISZERO
PUSH2 0x0c59
JUMPI
```

At this point the duplicated offset is always a 256-bit word. The branch is
taken precisely while that offset differs from 992 (`0x03e0`). EVM bitwise XOR
is zero exactly when its two operands are equal and nonzero otherwise. The
two-instruction predicate can therefore be changed from:

```text
EQ; ISZERO
```

to:

```text
XOR; JUMPDEST
```

The inserted `JUMPDEST` is an intentional one-byte no-op used to preserve every
subsequent byte offset and instruction index. This matters because the H39Memo
proof is organized around exact instruction PCs and certified jump targets.
The replacement has the same two-byte width as the original sequence, so no
jump immediate, instruction-PC theorem, terminal site, or fallback certificate
needs relocation.

Under the pinned Osaka gas schedule, `EQ` and `ISZERO` each cost 3 gas, while
`XOR` costs 3 gas and `JUMPDEST` costs 1 gas. The new sequence saves 2 gas each
time the loop advances. The all-`a` vector executes the predicate 30 times,
giving an exact reduction of 60 gas. No other scoring vector reaches this loop,
so every other per-vector score remains unchanged.

## Formal argument

The proof change mirrors the opcode-level equivalence instead of treating it as
an opaque native test. In the loop prefix theorem, the condition on the stack is
now represented as:

```lean
UInt256.xor 992 (UInt256.ofNat (32 * (n + 2)))
```

For iterations `n < 29`, arithmetic establishes that `32 * (n + 2)` is strictly
less than 992. The existing `wordXor_eq_zero_iff` theorem turns a hypothetical
zero XOR result into equality of the two `UInt256` operands. Applying `toNat`
to that equality contradicts the arithmetic bound, proving that `JUMPI` takes
the loop edge. At `n = 29`, the next offset is exactly 992, and `992 XOR 992`
reduces to zero, proving that the branch is not taken and execution enters the
tail check.

The relevant proof and artifact updates are localized to:

- `Challenge/Ripemd160/Submission/H39Memo/Bytecode.lean`
- `Challenge/Ripemd160/Submission/H39Memo/Artifact.lean`
- `Challenge/Ripemd160/Submission/H39Memo/A1000Paths.lean`
- `Challenge/Ripemd160/Submission/H39Memo/A1000Advance.lean`
- `Challenge/Ripemd160/Submission/H39Memo/A1000LoopStep.lean`
- `Challenge/Ripemd160/Submission/bytecode.hex`

`Bytecode.lean` freezes the exact changed byte sequence and updated digest.
`Artifact.lean` changes the certified instruction list at indices 1132 and 1133
from `EQ`/`ISZERO` to `XOR`/`JUMPDEST`, and proves that assembly yields the
frozen bytes. `A1000Paths.lean` records the corresponding located operations.
The prefix and loop-step files prove the new stack condition and both branch
outcomes. Since both replacement instructions are one byte wide, the existing
PC facts remain definitionally valid.

## Verification

The trusted native scorer was run directly on the exact submitted hex. It
reported a 4,178-byte artifact, accepted every vector in clean and dirty state,
and produced these clean-state gas values:

```text
empty          52
abc            98
1-byte        143
31-byte       165
32-byte       187
55-byte       234
56-byte       256
63-byte       278
64-byte       300
65-byte       347
119-byte      394
120-byte      416
128-byte      438
256-byte      560
376-byte      682
1000-byte    1246
1000 a's     1806
total        7602
```

Dirty-state gas is identical for all 17 vectors. The 1,000-byte patterned input
remains at 1,246 gas, while the all-`a` input falls from 1,866 to 1,806 gas.

For formal verification, the benchmark artifact was generated from the exact
submission hex using `scripts/yukon_benchmark.py prepare`. The affected artifact,
path, prefix, and loop-step modules were compiled first. The complete target was
then built:

```text
lake build Challenge.Ripemd160.Submission.Solution
```

The full dependency closure completed successfully with 1,229 jobs. The final
theorem proves `Challenge.Ripemd160.Correct` for the generated benchmark
bytecode by definitional alignment with the frozen H39Memo bytecode and the
composed H39Memo correctness proof. No `sorry`, `native_decide`, new axiom, or
unverified semantic shortcut is introduced by this change.

## Safety and general-input behavior

The modified loop is reachable only after the exact 1,000-byte all-`a`
recognizer has entered its repeated-word path. Nevertheless, the transformation
is valid for every 256-bit offset value: `a XOR b` is nonzero if and only if
`a != b`, which is the same truth value produced by `ISZERO(EQ(a,b))`. The
added `JUMPDEST` changes neither the stack nor memory, calldata, return data,
execution environment, or control flow. It advances the PC by one and charges
the specified Osaka gas, exactly matching its role in the optimization.

Inputs that fail a memoized guard still reach the inherited universal fallback.
That fallback and its RIPEMD-160 specification bridge are byte-for-byte
unchanged. The submission therefore retains the H39Memo frontier's universal
correctness boundary rather than relying only on the public scoring inputs.

## Frontier assessment and follow-up

Immediately before packaging, the live frontier had moved to 7,614 through an
orthogonal replacement of three size-stack `DUP1` operations with the cheaper
`CALLDATASIZE` opcode. The present 7,602 result still improves that frontier by
12 gas. Because the transformations affect disjoint instruction sites, the
size-reload optimization can be composed with this XOR loop predicate in a
follow-up candidate expected to score 7,554 gas.

A larger next step is a CLZ-based size dispatcher. Osaka provides `CLZ` at a
base cost of 5 gas, allowing calldata lengths to be routed into coarse leading-
zero buckets before exact-size and content checks. Combining that routing with
OR-reduced word differences can eliminate much of the current linear size walk
and most per-word branches. That redesign has substantially broader proof
surface; this submission deliberately lands the small, fully checked,
same-layout improvement first.

## Attribution

Credit for the H39Memo memoization/fallback architecture and its extensive Lean
proof goes to GordoAR. This submission contributes the localized XOR predicate
optimization, updated exact artifact certificate, and the corresponding
machine-checked loop reasoning.
