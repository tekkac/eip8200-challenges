# Fast-path proof conventions (read before writing any Lean)

Repository: /home/ubuntu/eip8200-challenges
Artifact:   Challenge/Modexp/Submission/bytecode.hex  (2901 bytes, 1768 instructions)
Disassembly of the appended region: /home/ubuntu/work/fastdis.txt
  columns: `index  pc  mnemonic  operand`, index 0 = first instruction of the whole image.
Appended fast path: instruction indices 977..1767, pc 1314..2900.
  Indices 1742..1767 (pc 2863..2900) are `CCB`, which replaced the second
  `DOUBLE256` call; the only edit to the pre-existing bytes was the PUSH2
  operand at pc 1552..1553 (0x0777 -> 0x0B2F), so every earlier index and pc
  is unchanged.

DO NOT BUILD `Challenge.Modexp.Submission.Proofs.Fast.Paths` or
`...Fast.Paths.P2`.  Nothing imports the `Paths` aggregator, and `P2.lean`
(`blk1039`, a 99-instruction block) has never compiled.  Build the leaf
modules by name instead: `...Fast.Setup`, `...Fast.Exp`, `...Fast.Ccb`,
`...Fast.Correct`.

The design notes are /home/ubuntu/work-mont/PROOF_PLAN.md (section `## Simple variant`)
and /home/ubuntu/work-mont/simple/BLOCKS_simple.md.  THOSE USE A DIFFERENT BASE:
their instruction indices are 16 LOWER and their pcs are 30 LOWER than the real
artifact.  Always re-derive indices and pcs from /home/ubuntu/work/fastdis.txt,
never copy them from the plan.

## Foundation already in place

`Challenge/Modexp/Submission/Proofs/Fast/Defs.lean` (namespace
`Challenge.Modexp.Submission.Proofs.Fast`) provides:

* `opAt (index) (op)` and `pushAt (index) (width) (value)` producing
  `Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka`;
* `@[simp] fastPC0 … fastPC19`, the program-counter table for indices 977..1741,
  each stated as `Artifact.submissionArtifact.instructionPC i = [..][i - lo]!`
  with `lo ≤ i ≤ hi` side conditions;
* `jumpDest<pc>` for every jump destination the fast path uses, e.g. `jumpDest1196`.

Reusable, already built:
* `Challenge.EvmProof.Stepper` — `runLocatedBlock`, `runLocatedBlock_sound`,
  `runLocated`, `runInstr`, `Located`;
* `Challenge.EvmProof.GasSteps` — `.trans`, `.cast`, `.iterateBounded`;
* `Challenge.Modexp.Submission.Proofs.Limbs` — `Limbs.Represents memory ptr count value`,
  `Limbs.memoryLimbs`, `Limbs.radix`, and the value lemmas;
* `Challenge.EvmProof.Memory` — `readWord_writeWord`, disjointness lemmas;
* `Challenge.EvmProof.Word` — `word_toNat_ofNat`, `ofNat_add_mod`, `succ_ofNat_mod`,
  `word_toNat_isZero`, `word_eq_ofNat_toNat`, …

## Style to copy

Follow `Challenge/Modexp/Submission/Proofs/Bytecode/BigHelpers.lean` exactly:

1. one `def <name>Path : List (Located Artifact.submissionArtifact .Osaka)` per basic
   block, listing every instruction with `opAt`/`pushAt`;
2. one `def <name>State ... : State` per block boundary, written as
   `{ s with pc := UInt256.ofNat <pc>, stack := [...] ++ rest, memory := …, activeWords := … }`;
3. one `theorem run_<name> ... : runLocatedBlock <name>Path <entryState> = some <exitState>`
   proved with `set_option linter.unusedSimpArgs false in` and
   `simp (config := { maxSteps := 500000 }) (disch := omega) [ <path>, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
     Challenge.EvmProof.Stepper.runInstr, <state defs>, fastPC<k>, hcode, hrun, <jumpDest>,
     Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, List.exchange,
     Nat.add_assoc, … ]`;
4. one `def gasSteps_<name> ... : GasSteps <entry> <exit>` composing the block lemmas
   with `Challenge.EvmProof.Stepper.runLocatedBlock_sound` and `.trans`.  When the
   starting state is not syntactically the one Lean infers, pass `(s := …)` explicitly.
5. loops: `Challenge.EvmProof.GasSteps.iterateBounded` over an indexed state family,
   exactly as `BigHelpers.gasSteps_addLoop` does.

Do NOT write any `_cost_potential` / closed-form gas theorem.  Only the existence of a
`GasSteps` trace is needed.  Never use `sorry`, `native_decide`, or any axiom beyond
`propext`, `Quot.sound`, `Classical.choice`.

## Memory map (absolute byte addresses, independent of the code offset)

```
M     0x0000   modulus, n limbs (big-endian limb order: offset 0 is the MOST significant limb)
ACC   0x0400   accumulator, n limbs
BASE  0x0800   base in Montgomery form, n limbs
ONE   0x0C00   single-limb scratch, n limbs
R1    0x1000   phi(1) = R mod m, n limbs
CC    0x1400   phi(radix) = radix * R mod m, n limbs
RR    0x1800   R^2 mod m, n limbs
SUBB  0x1C00   subtraction candidate, n limbs
T_    0x2000   CIOS t[n+1]
TN    0x2020   CIOS t[n]
TS    0x2040   CIOS t[n-1..0], n limbs;  TL = 0x2020 + s32 is the address of t[0]
V_S32 0x2480   32*n
V_MINV 0x24A0  -m[0]^{-1} mod 2^256
V_ML  0x24C0   s32 - 32   (offset of the least significant modulus limb)
V_TL  0x24E0   0x2020 + s32
V_EOFF 0x2500  96 + bsize
V_N   0x2520   n
```

`n = ceil(msize/32)`, `s32 = 32*n`, `2 ≤ n ≤ 32`, `radix = 2^256`.
Every n-limb block at address `A` holds its MOST significant limb at `A` and its least
significant limb at `A + s32 - 32`; `Limbs.Represents memory A n v` is stated with the
project's existing little-endian-index convention, so a block at `A` in this program
corresponds to `Limbs.Represents` at `A` with the limb order reversed — state your own
`FastRepresents memory A n v` in `Fast/Model.lean` if that is cleaner, and prove the
bridge once.

## Fast-path precondition (decided by indices 977..1038, before any memory write)

```
P1  msize > 32
P2  bsize ≤ 1024 ∧ esize ≤ 1024 ∧ msize ≤ 1024      (also implied by ValidInput)
P3  the top limb of m is nonzero, i.e. m ≥ radix^(n-1)
P4  m is odd
```
If any fails the code pops its stack and executes `PUSH2 1196; JUMP`, reaching pc 1196
with an EMPTY stack, memory untouched and `activeWords = 0` — the state the existing
`Challenge.Modexp.Submission.Proofs.Bytecode.Main` proof starts its header block from.

## File ownership (do not edit files you do not own)

```
Fast/Defs.lean      done, do not edit
Fast/Model.lean     pure arithmetic model + FastRepresents bridge
Fast/Csub.lean      ADDMOD and CSUB subroutines
Fast/Double.lean    DOUBLE256 subroutine
Fast/Monpro.lean    MONPRO (CIOS) subroutine
Fast/Setup.lean     entry checks, bail, modulus load, minv, R1/CC construction
Fast/Exp.lean       RR chain, base chain, exponent loop, final MonPro, RETURN
Fast/Correct.lean   top-level: fast-path trace + dispatch against the existing proof
```

## Building — IMPORTANT, the machine has only 30 GB of RAM

A single Lean module in this project can peak above 20 GB, so two concurrent builds
freeze the machine.  NEVER call `lake` or `lean` directly.  Build only with

```
/home/ubuntu/work/safebuild.sh Challenge.Modexp.Submission.Proofs.Fast.<Module>
```

which takes a global lock (so builds run one at a time across all agents) and caps the
build at 14 GB so a runaway elaboration is killed instead of taking the machine down.
It may block for many minutes waiting for the lock — that is expected and correct; wait
for it rather than starting a second build.  Do not run any other memory-hungry command
while a build is in flight.  Never run `yukon` anything.  Never edit `Challenge/Modexp/Submission/bytecode.hex`,
`Bytes.lean` or `Proofs/Bytecode/Artifact.lean`.

## Working discipline — non-negotiable

The machine has 30 GB of RAM and a single unverified Lean file has already taken the
whole machine down.  Therefore:

* **Never let a file grow while unverified.**  Write at most ~50 lines, build, fix, and
  only then write the next chunk.  A file that has never compiled is worthless; a file
  that compiles after every increment is progress you cannot lose.
* Build only with `/home/ubuntu/work/safebuild.sh <Module> [timeout-seconds]`.  It takes
  a global lock, caps memory at 22 GB and kills the build after the timeout, printing
  `SAFEBUILD: KILLED` or `SAFEBUILD: TIMED OUT`.  If you see either, you have written
  something whose elaboration diverges — do not raise the timeout, simplify the code.
* Common cause of divergence in this project: a `State`-valued definition containing an
  `if`, or a deeply nested chain of record updates.  `whnf` then tries to decide the
  condition or unfold the chain hundreds of times.  Keep block-boundary states shallow,
  state reduction lemmas over an arbitrary state constrained by `pc`/`stack` hypotheses,
  and mark any bit-extraction helper `@[irreducible]` before it appears under an `if`.
* Earlier drafts of `Setup.lean` and `Double.lean` are in `/home/ubuntu/work/fast-drafts/`.
  They are UNVERIFIED and at least one of them diverges.  Mine them for block layouts and
  state definitions if useful, but re-derive and re-verify everything incrementally.

## Ready-made block paths — use these, do not retype them

`Challenge.Modexp.Submission.Proofs.Fast.Paths` (split across
`Fast/Paths/P0.lean` … `Fast/Paths/P13.lean`, all in namespace
`Challenge.Modexp.Submission.Proofs.Fast`) already contains, mechanically generated
from the frozen artifact and verified to elaborate, one definition per basic block:

```lean
def blk<i> : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka)
```

where `<i>` is the instruction index of the block's FIRST instruction.  Blocks break at
every `JUMPDEST` and after every `JUMP`/`JUMPI`/`RETURN`/`INVALID`/`STOP`.  The full list
with index and pc ranges is `/home/ubuntu/work/fastblocks.txt`.

Import only the group you need (e.g. `import Challenge.Modexp.Submission.Proofs.Fast.Paths.P5`)
rather than the umbrella `Fast.Paths`, so your module does not pull in blocks it never
mentions.  Writing 60 `opAt`/`pushAt` entries in one file is what blew the memory cap
before, so never re-inline a block path by hand — use `blk<i>`.

Your job is therefore only: the `State` constructors at block boundaries, the
`run_*` reduction lemmas (`runLocatedBlock blk<i> <entry> = some <exit>`), the loop
invariants, and the `GasSteps` composition.

## Build wrapper fixed (2026-09-04)

Earlier `SAFEBUILD: KILLED` results were mostly NOT a single module diverging.  The
cause was `lake build`'s own module-level parallelism: it elaborates several heavy
modules at once and their combined footprint exceeds the machine.  `safebuild.sh` now
routes through `scripts/build-lean-serial.sh`, which gives each module its own Lake
process in dependency order, so only one module elaborates at a time.

If you previously simplified a proof only to get past a `KILLED`, that simplification
may not have been necessary — but do not undo it unless you have a reason; a smaller
proof is still cheaper.  A `KILLED` from now on really does mean the single module you
are building is too big, and a `TIMED OUT` really does mean it diverges.
