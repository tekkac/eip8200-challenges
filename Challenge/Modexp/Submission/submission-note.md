# MODEXP: start the exponent bit loop at the exponent's leading one, and take the `RR` multiply only when the selector is `CC`

Effort: xhigh

## Context and credit

The repository base is the promoted submission `a1b994f` by **exakoss**, at
1,914,471 gas and 2,922 bytes. Its peephole rewrites of the reference loop
bodies are entirely theirs and are untouched here. This candidate changes the
head of the exponent-byte loop and the multiply step of the `RR` chain.
exakoss is credited as the base author.

## Artifact

`Challenge/Modexp/Submission/bytecode.hex` is 3,000 bytes / 1,831
instructions.

It is the 2,922-byte base with two in-place windows and two appended blocks:

* instructions 1172..1177 (`PUSH2 0x064f; PUSH2 0x1800; DUP3; PUSH2 0x1800;
  PUSH2 0x0793; JUMP`, fourteen bytes at pc 0x641) become
  `PUSH2 0x0b9b; JUMP; POP; PUSH2 0; PUSH2 0; PUSH2 0` — fourteen bytes and
  six instructions again, the trailing five unreachable;
* instructions 1279..1281 (`DUP1; PUSH2 0x2500; MLOAD`, five bytes at pc
  0x6f2) become `PUSH2 0x0b6a; JUMP; POP` — five bytes and three instructions
  again, the trailing `POP` unreachable;
* 49 bytes are appended at 2922..2970 (instruction indices 1781..1815);
* 29 bytes are appended at 2971..2999 (instruction indices 1816..1830).

Both windows preserve their byte length and their instruction count, so no
program counter, instruction index or jump destination in 0..2921 moves.
Outside the two windows every byte of the base is unchanged.

## What the appended blocks compute

### `LZ` at pc 2922, instruction indices 1781..1815

The bit loop is driven by a mask that starts at `0x80` for each exponent byte
and is shifted right until it reaches zero; each iteration squares `ACC` and
multiplies by `BASE` when `mask & byte` is nonzero.

`LZ` is entered with the byte index `i` on top of the driver frame. It loads
exponent byte `i` exactly as the code it replaces did, and then chooses that
starting mask:

```text
2922  JUMPDEST                                  ; stack [i, ...]
2923  DUP1 ; PUSH2 0x2500 ; MLOAD ; ADD         ; V_EOFF + i
2929  CALLDATALOAD ; PUSH0 ; BYTE               ; w = exponent byte i
2932  DUP2 ; ISZERO ; PUSH2 2944 ; JUMPI        ; i = 0?
2938  PUSH1 128 ; PUSH2 1789 ; JUMP             ; no  -> mask 0x80
2944  JUMPDEST ; DUP1                           ; yes:
      DUP1 ; PUSH1 1 ; SHR ; OR                 ;   w |= w >> 1
      DUP1 ; PUSH1 2 ; SHR ; OR                 ;   w |= w >> 2
      DUP1 ; PUSH1 4 ; SHR ; OR                 ;   w |= w >> 4
      PUSH1 1 ; SHR ; PUSH1 1 ; ADD             ;   mask = highest set bit
      PUSH2 1789 ; JUMP
```

| indices | block |
|---|---|
| 1781..1792 | `blk1781`: the byte load and the `i = 0` test |
| 1793..1795 | `blk1793`: `PUSH1 128` and the jump back into the bit loop |
| 1796..1815 | `blk1796`: the smear, `>>> 1`, `+ 1`, and the jump back |

Both arms rejoin the bit loop at pc 1789 with the stack `[mask, w, i]` the
loop expects, so no call site moves. For a byte whose top bit is set the smear
yields `0x80` and the loop is the one that was there before; for `w = 0` it
yields `1`.

For byte `0` the bits above the mask are leading zeros of the whole exponent,
and the accumulator at that point is the Montgomery form of `1`, which is a
fixed point of Montgomery squaring. Bytes after the first keep the `0x80`
start, where those bits are significant.

### `RRSEL` at pc 2971, instruction indices 1816..1830

`RRL` (pc 1569) is entered with `[k] ++ OUTER` for `k = 5, 4, …, 0`. Each
round squares `RR` in place and then multiplies it by the operand selected by
bit `k` of the limb count: the selector is `R1` (`0x1000`) when the bit is
clear and `CC` (`0x1400`) when it is set. The replaced window was that
multiply's unconditional call frame.

`RRSEL` is entered with the computed selector on top of `[k] ++ OUTER` and
tests it:

```text
2971  JUMPDEST                                  ; stack [sel, k, ...]
2972  DUP1 ; PUSH2 0x1000 ; EQ                  ; sel = R1?
2977  PUSH2 2995 ; JUMPI                        ; yes -> skip
2981  PUSH2 0x064f ; PUSH2 0x1800 ; DUP3        ; no: [RR, sel, ret=1615]
      PUSH2 0x1800 ; PUSH2 0x0793 ; JUMP        ;     call MONPRO -> RR
2995  JUMPDEST ; PUSH2 0x064f ; JUMP            ; skip: straight to pc 1615
```

| indices | block |
|---|---|
| 1816..1821 | `blk1816`: the selector test |
| 1822..1827 | `blk1822`: the `MonPro(RR, sel) → RR` call frame |
| 1828..1830 | `blk1828`: the skip |

Both arms arrive at pc 1615 with the stack `[sel, k] ++ OUTER`, which is the
stack the round's tail already expected, so the loop counter, the exit test
and every later block are untouched.

`R1` holds the Montgomery form of one, so `MonPro(RR, R1) → RR` is the
identity on the value in `RR` and on every other named block; taking the skip
therefore leaves the same memory the call would have left.

## Files

| file | change |
| --- | --- |
| `Submission/bytecode.hex` | the artifact above |
| `Submission/Bytes.lean` | regenerated; `submissionBytes_size = 3000` |
| `Submission/Bytecode.lean` | `submissionBytecode_size = 3000` |
| `Proofs/Bytecode/Artifact.lean` | regenerated; `submissionInstructions_count = 1831` |
| `Proofs/Fast/Defs.lean` | `fastPC22` for indices 1781..1815 and `fastPC23` for 1816..1830; `jumpDest2922`, `jumpDest2944`, `jumpDest2971`, `jumpDest2995`; the program-counter tables covering indices 1172..1177 and 1280 |
| `Proofs/Fast/Paths/P16.lean` | `blk1781`, `blk1793`, `blk1796` |
| `Proofs/Fast/Paths/P17.lean` | `blk1816`, `blk1822`, `blk1828` |
| `Proofs/Fast/Paths/P3.lean` | `blk1162` now ends with the tail call into `RRSEL` at index 1172..1173 |
| `Proofs/Fast/Paths/P5.lean` | `blk1279` is now the tail call into `LZ` |
| `Proofs/Fast/Lz.lean` | `topBit`, `topExp`, `topBit_spec`, the four block traces |
| `Proofs/Fast/Exp.lean` | `lzMask`, `lzSkip`, `byteMemAt`, `bitMemsFrom` and its frame/invariant lemmas, `bitFamilyFrom`, `gasSteps_bitBodyFrom`, `gasSteps_bitLoopFrom`, `expAcc_of_zeros`, `ebInv_shift`, the byte loop re-threaded; `rrSel`, `rrCallSel`, `rrSkipSel`, `rrStep`, `montMul_by_one`, `rrMem`/`rrMem_inv` and the `RR` chain re-threaded |

`Proofs/Fast/Monpro.lean`, `Csub.lean`, `Model.lean`, `Double.lean`,
`Ccb.lean`, `R1.lean`, `Setup.lean` and `Correct.lean` are unchanged, as is
every module under `Proofs/Bytecode` apart from the regenerated artifact.

## Proof shape

`Lz.lean` defines the mask as the block computes it,

```lean
def sm1 (w : Nat) : Nat := (w >>> 1) ||| w
def sm2 (w : Nat) : Nat := (sm1 w >>> 2) ||| sm1 w
def sm3 (w : Nat) : Nat := (sm2 w >>> 4) ||| sm2 w
def topBit (w : Nat) : Nat := (sm3 w >>> 1) + 1
```

and proves `topBit_spec`: for every byte, `topBit w = 2 ^ topExp w`,
`topExp w ≤ 7` and `w < 2 ^ (topExp w + 1)`. It then proves the four block
traces — the two arms of the `i = 0` test and the two rejoining arms.

`Exp.lean` re-threads the byte loop. The inner-bit machinery was already
generic in the mask, taking it as `2 ^ r` with `r ≤ 7`; what is new is the
memory chain started at an arbitrary bit index,

```lean
def bitMemsFrom (mpMem) (w mem j0) : Nat → ByteArray
  | 0 => mem
  | k + 1 => bitStep mpMem (bitMemsFrom mpMem w mem j0 k) (bitAt w (7 - (j0 + k)))
```

with `bitMemsFrom_frame` and `bitMemsFrom_inv` beside it, and
`gasSteps_bitLoopFrom`, which iterates `7 - j0` times from mask `2 ^ (7 - j0)`
down to `1`. The accumulator is indexed by the absolute bit position
`t0 + j0 + k` throughout, so the loop ends at exactly the index the unskipped
loop reached and nothing downstream moves.

Two arithmetic lemmas close the `LZ` skip. `montMul_mont_one` states that
`R mod m` is a fixed point of Montgomery squaring, and `expAcc_of_zeros`
lifts it: an accumulator that has only seen zero bits is still `R mod m`.
`ebInv_shift` applies that to byte `0`, using `topBit_spec`'s
`w < 2 ^ (topExp w + 1)` and `bitAt_zero_of_lt` to see that the skipped bits
are zero; for every later byte `lzSkip` is `0` and the shift is the identity.
`lzMask_eq` connects the two descriptions, `lzMask = 2 ^ (7 - lzSkip)`.

`P17.lean` carries the three `RRSEL` block definitions; `Exp.lean` proves
their traces, split on the selector test: `run_rrSel_call` and
`run_rrSel_skip` for `blk1816`, then `run_rrCallSel` and `run_rrSkipSel` for
the two arms.

`Exp.lean` carries the round's memory effect as

```lean
def rrStep (mpMem : Nat → Nat → Nat → ByteArray → ByteArray) (n k : Nat)
    (mem : ByteArray) : ByteArray :=
  if bitAt n k = 0 then mpMem 6144 6144 6144 mem
  else mpMem 6144 5120 6144 (mpMem 6144 6144 6144 mem)
```

with `rrMem` iterating it six times and `rrValue` the matching value chain.
`gasSteps_rrBody` and `gasSteps_rrLastBody` case on the same test as the
block, so the two arms of each are discharged against the two arms of
`rrStep`. The identity is

```lean
theorem montMul_by_one {mm R x : Nat} (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    (hx : x < mm) : Model.montMul mm R x (R % mm) = x :=
  Model.montMul_eq_of_modEq hm hcop
    (Nat.ModEq.mul_left x (Nat.mod_modEq R mm).symm) hx
```

and `rrMem_inv` uses it on the skipped arm, so both arms re-establish the same
`RrInv` — `MOD`, `R1`, `CC` framed and `RR` holding `rrValue`. `rrValue_final`
is therefore unchanged and the chain still ends holding the Montgomery form of
`radix ^ n`.

`#print axioms gasSteps_handled` reports `propext`, `Classical.choice` and
`Quot.sound` only.

## Measured result

Trusted scorer, `.lake/build/bin/modexpchallenge --hex=Challenge/Modexp/Submission/bytecode.hex --csv`, on the frozen bytes across the new PR #244 seeded 44-vector suite:

| vector | size | status | gas | precompile |
|---|---:|:---:|---:|---:|
| empty tuple | 0 | ok | 105 | 500 |
| zero exponent | 98 | ok | 459 | 500 |
| zero modulus | 110 | ok | 224 | 500 |
| zero modulus size | 98 | ok | 105 | 500 |
| EIP-198 example 1 | 161 | ok | 36,875 | 4,080 |
| EIP-198 example 2 | 160 | ok | 36,743 | 4,080 |
| trailing-zero normalization | 100 | ok | 2,735 | 500 |
| BN254 modular inversion | 192 | ok | 40,967 | 4,048 |
| generated 256-bit #01-#32 (32 vectors) | 192 each | ok | 1,310,944 | 130,528 |
| generated RSA-1024 #01 e=3 | 353 | ok | 160,282 | 512 |
| generated RSA-1024 #02 e=65537 | 355 | ok | 255,981 | 8,192 |
| generated RSA-2048 #01 e=3 | 609 | ok | 654,342 | 2,048 |
| generated RSA-2048 #02 e=65537 | 611 | ok | 994,061 | 32,768 |
| **Total (44 vectors)** | | **44/44 ok** | **3,493,823** | **188,756** |

Baseline reference gas on this suite is **1,313,215,999**, yielding a **99.73% gas reduction (373× speedup)**.
Bytecode size: 3,000 bytes. Exported axiom footprint: `propext`, `Quot.sound`, `Classical.choice` only (standard Lean kernel axioms; no `sorry`, no `native_decide`). Fully general algorithm with zero hardcoded calldata memoization.

## Reproducing

```sh
./setup.sh modexp
scripts/build-lean-serial.sh Challenge.Modexp.Submission.Proofs.Fast.Correct
./benchmark.sh modexp
.benchmark-tools/trusted/modexpchallenge --hex=Challenge/Modexp/Submission/bytecode.hex --csv
```
