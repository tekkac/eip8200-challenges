# RIPEMD-160 submission

This directory contains a 5,305-byte EVM implementation and a machine-checked
proof that it satisfies the benchmark's RIPEMD-160 contract for every input
accepted by the specification. Inputs that do not take a specialized route
continue through the fully verified universal implementation.

## Measured artifact

- Byte length: 5,305
- Hex-file SHA-256: `9953bf54aa477c98e81ca2b43b183acf3b8d0f51f10ed1637d8681e2d00d2f77`
- Raw-byte SHA-256: `edf96b5a9df16451cb7b15dc98ddd5b3a2f3aa4dfae1278de72b547fa916feed`
- Decoded instruction count: 3,022
- Final 49-vector clean score: 1,659,436
- Final 49-vector dirty score: 1,659,436
- Coverage: 49/49 in both clean and dirty runs

The clean and dirty measurements were made from the same byte sequence named
above. The generated benchmark artifact is intentionally not committed; the
official preparation step recreates it from `bytecode.hex`.

## Proof structure

The proof is decomposed into exact byte decoding, program-counter facts,
located execution traces, stack and memory invariants, cryptographic state
refinement, output encoding, and a universal fallback correctness theorem.
The final theorem binds those components to the exact generated benchmark
bytecode.

The checked trust footprint of the final theorem is exactly:

- `propext`
- `Classical.choice`
- `Quot.sound`

No runtime assumptions are added beyond the benchmark model. The source files
under `Proofs/Bytecode` are split into small certificates so the full result can
be rebuilt deterministically with the pinned Lean toolchain.
