import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P14
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# The `CCB` subroutine of the appended Montgomery path

`CCB` occupies instruction indices 1742..1767 (pc 2863..2900).  It is entered
at pc 2863 with stack `[px, ret]`, exactly the calling convention of
`DOUBLE256`, and leaves the `n`-limb block at `px` holding `x * radix mod m`
— the same postcondition — but it reaches it with one `ADDMOD` and eight
`MONPRO` calls instead of 256 `ADDMOD` calls.

The reason it can: `MonPro` needs only `V_MINV`, never `R1`, so once the block
at `px` holds a Montgomery residue `x` its square under `MonPro` is the residue
of the square.  Doubling once turns `R mod m` into the residue of `2`, and
eight Montgomery squarings turn that into the residue of `2 ^ (2 ^ 8)`, i.e.
`radix * R mod m`.

The five basic blocks are

* `blk1742` (idx 1742..1748, pc 2863..2873) — `JUMPDEST`, then the call frame
  `[px, px, px, 2874]` and a jump to `ADDMOD` (pc 2467);
* `blk1749` (idx 1749..1750, pc 2874..2876) — `JUMPDEST; PUSH1 8`;
* `blk1751` (idx 1751..1757, pc 2877..2887) — the loop head `CCL`, which
  pushes the call frame `[px, px, px, 2888]` and jumps to `MONPRO` (pc 1939);
* `blk1758` (idx 1758..1764, pc 2888..2897) — the return point, which
  decrements the counter and jumps back to pc 2877 while it is nonzero;
* `blk1765` (idx 1765..1767, pc 2898..2900) — `POP; POP; JUMP ret`.

`ADDMOD` and `MONPRO` enter only through abstract single-step contracts, so
this module depends on neither `Fast.Csub` nor `Fast.Monpro`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Ccb

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

-- Lean 4.31 ships `List.getElem?_cons_zero` without the `simp` attribute, so the
-- program-counter tables of `Fast.Defs` (which end in `[…][i - lo]!`) do not
-- reduce inside the block-reduction `simp` calls without it.
attribute [local simp] List.getElem?_cons_zero

/-! ## States at the block boundaries -/

/-- The live part of the stack inside the loop: the counter, the block pointer
and the caller's return address. -/
def loopStack (px k : Nat) (ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat k, UInt256.ofNat px, ret] ++ rest

/-- Subroutine entry, pc 2863, stack `[px, ret]`. -/
def entryState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2863
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- The prologue `ADDMOD` call, pc 2467, frame `[px, px, px, 2874]`. -/
def amCallState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2467
           stack := [UInt256.ofNat px, UInt256.ofNat px, UInt256.ofNat px,
                     UInt256.ofNat 2874] ++ ([UInt256.ofNat px, ret] ++ rest)
           memory := mem }

/-- The prologue return point, pc 2874, stack `[px, ret]`. -/
def postState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2874
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- The loop head `CCL`, pc 2877, with the counter at `k`. -/
def loopState (s : State) (mem : ByteArray) (px k : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2877
           stack := loopStack px k ret rest
           memory := mem }

/-- The `MONPRO` call, pc 1939, with the frame `[px, px, px, 2888]` pushed. -/
def mpCallState (s : State) (mem : ByteArray) (px k : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1939
           stack := [UInt256.ofNat px, UInt256.ofNat px, UInt256.ofNat px,
                     UInt256.ofNat 2888] ++ loopStack px k ret rest
           memory := mem }

/-- The return point, pc 2888, with the counter still at `k`. -/
def retState (s : State) (mem : ByteArray) (px k : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2888
           stack := loopStack px k ret rest
           memory := mem }

/-- The loop exit, pc 2898, with the counter at zero. -/
def exitState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2898
           stack := loopStack px 0 ret rest
           memory := mem }

/-- Back at the caller, pc `ret`, with the frame popped. -/
def doneState (s : State) (mem : ByteArray) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := ret
           stack := rest
           memory := mem }

/-! ## Block reductions -/

set_option linter.unusedSimpArgs false in
/-- `blk1742` (pc 2863..2873): push the `ADDMOD` frame and jump to pc 2467. -/
theorem run_entry (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1742
      (entryState s mem px ret rest) =
      some (amCallState s mem px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have h2874 : (2874 : UInt256) = UInt256.ofNat 2874 := by decide
  have h2467 : (2467 : UInt256) = UInt256.ofNat 2467 := by decide
  have h2467Nat : (UInt256.ofNat 2467).toNat = 2467 := by decide
  simp (config := { maxSteps := 400000 }) [blk1742, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    entryState, amCallState, fastPC20, hc2, hc3, hc4, hc5, hc6, hc7, hcode, hrun,
    h2874, h2467, h2467Nat, jumpDest2467,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1749` (pc 2874..2876): push the squaring counter. -/
theorem run_post (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1749
      (postState s mem px ret rest) =
      some (loopState s mem px 8 ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have h8 : (8 : UInt256) = UInt256.ofNat 8 := by decide
  simp (config := { maxSteps := 200000 }) [blk1749, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    postState, loopState, loopStack, fastPC20, hc2, hrun, h8,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1751` (pc 2877..2887): push the `MONPRO` frame and jump to pc 1939. -/
theorem run_call (s : State) (mem : ByteArray) (px k : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1751
      (loopState s mem px k ret rest) =
      some (mpCallState s mem px k ret rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have h2888 : (2888 : UInt256) = UInt256.ofNat 2888 := by decide
  have h1939 : (1939 : UInt256) = UInt256.ofNat 1939 := by decide
  have h1939Nat : (UInt256.ofNat 1939).toNat = 1939 := by decide
  simp (config := { maxSteps := 400000 }) [blk1751, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopState, mpCallState, loopStack, fastPC20, hc3, hc4, hc5, hc6, hc7, hc8,
    hcode, hrun, h2888, h1939, h1939Nat, jumpDest1939,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1758` (pc 2888..2897), counter above one: decrement and loop. -/
theorem run_ret (s : State) (mem : ByteArray) (px k k' : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hk : k = k' + 1) (hk' : 1 ≤ k') (hk8 : k ≤ 8)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1758
      (retState s mem px k ret rest) =
      some (loopState s mem px k' ret rest) := by
  subst hk
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h2877 : (2877 : UInt256) = UInt256.ofNat 2877 := by decide
  have h2877Nat : (UInt256.ofNat 2877).toNat = 2877 := by decide
  have hsub : UInt256.ofNat (k' + 1) - UInt256.ofNat 1 = UInt256.ofNat k' := by
    have h := Challenge.EvmProof.Word.ofNat_sub_ofNat
      (a := k' + 1) (b := 1) (by omega) (by omega)
    rwa [Nat.add_sub_cancel] at h
  have htrue : UInt256.isTrue (UInt256.ofNat k') := by
    show (UInt256.ofNat k').toNat ≠ 0
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  simp (config := { maxSteps := 400000 }) [blk1758, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    retState, loopState, loopStack, fastPC20, hc3, hc4, hc5, hcode, hrun,
    hone, h2877, h2877Nat, hsub, htrue, jumpDest2877, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1758` (pc 2888..2897), counter one: fall through to the exit. -/
theorem run_retLast (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1758
      (retState s mem px 1 ret rest) =
      some (exitState s mem px ret rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h2877 : (2877 : UInt256) = UInt256.ofNat 2877 := by decide
  have hsub : UInt256.ofNat 1 - UInt256.ofNat 1 = UInt256.ofNat 0 := by decide
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  simp (config := { maxSteps := 400000 }) [blk1758, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    retState, exitState, loopStack, fastPC20, hc3, hc4, hc5, hrun,
    hone, h2877, hsub, hfalse, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1765` (pc 2898..2900): pop the frame and return to the caller. -/
theorem run_exit (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1765
      (exitState s mem px ret rest) =
      some (doneState s mem ret rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  simp (config := { maxSteps := 200000 }) [blk1765, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    exitState, doneState, loopStack, fastPC20, hc1, hc2, hc3, hcode, hjump, hrun,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

/-! ## Gas traces for the individual blocks -/

def gasSteps_entry (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entryState s mem px ret rest)
      (amCallState s mem px ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1742 hcode hfork
      (run_entry s mem px ret rest hcap hcode hrun) hrun hnp

def gasSteps_post (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (postState s mem px ret rest)
      (loopState s mem px 8 ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1749 hcode hfork
      (run_post s mem px ret rest hcap hrun) hrun hnp

def gasSteps_call (s : State) (mem : ByteArray) (px k : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (loopState s mem px k ret rest)
      (mpCallState s mem px k ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1751 hcode hfork
      (run_call s mem px k ret rest hcap hcode hrun) hrun hnp

def gasSteps_ret (s : State) (mem : ByteArray) (px k k' : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hk : k = k' + 1) (hk' : 1 ≤ k') (hk8 : k ≤ 8)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (retState s mem px k ret rest)
      (loopState s mem px k' ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1758 hcode hfork
      (run_ret s mem px k k' ret rest hcap hk hk' hk8 hcode hrun) hrun hnp

def gasSteps_retLast (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (retState s mem px 1 ret rest)
      (exitState s mem px ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1758 hcode hfork
      (run_retLast s mem px ret rest hcap hrun) hrun hnp

def gasSteps_exit (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (exitState s mem px ret rest)
      (doneState s mem ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1765 hcode hfork
      (run_exit s mem px ret rest hcap hcode hjump hrun) hrun hnp

/-! ## The squaring loop -/

/-- The indexed loop-head family: after `i` `MONPRO` calls the counter stands
at `8 - i`. -/
def loopFamily (s : State) (px : Nat) (ret : UInt256) (rest : List UInt256)
    (mems : Nat → ByteArray) (i : Nat) : State :=
  loopState s (mems i) px (8 - i) ret rest

/-- One loop iteration: call `MONPRO` and decrement the counter. -/
def gasSteps_iteration (s : State) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (mems : Nat → ByteArray)
    (monpro : ∀ i, i < 8 →
      Challenge.EvmProof.GasSteps (mpCallState s (mems i) px (8 - i) ret rest)
        (retState s (mems (i + 1)) px (8 - i) ret rest))
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (i : Nat) (hi : i < 7) :
    Challenge.EvmProof.GasSteps (loopFamily s px ret rest mems i)
      (loopFamily s px ret rest mems (i + 1)) :=
  ((gasSteps_call s (mems i) px (8 - i) ret rest hcap hcode hfork hrun hnp).trans
      (monpro i (by omega))).trans
    (gasSteps_ret s (mems (i + 1)) px (8 - i) (8 - (i + 1)) ret rest hcap
      (by omega) (by omega) (by omega) hcode hfork hrun hnp)

/-- The seven iterations that end at the loop head with the counter at one. -/
def gasSteps_loop (s : State) (px : Nat) (ret : UInt256) (rest : List UInt256)
    (mems : Nat → ByteArray)
    (monpro : ∀ i, i < 8 →
      Challenge.EvmProof.GasSteps (mpCallState s (mems i) px (8 - i) ret rest)
        (retState s (mems (i + 1)) px (8 - i) ret rest))
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (loopState s (mems 0) px 8 ret rest)
      (loopState s (mems 7) px 1 ret rest) :=
  Challenge.EvmProof.GasSteps.iterateBounded
    (I := loopFamily s px ret rest mems) 7
    (fun i hi => gasSteps_iteration s px ret rest mems monpro hcap hcode hfork hrun
      hnp i hi)

/-- **Execution certificate for `CCB`.**  Entering pc 2863 with stack
`[px, ret]` runs one `ADDMOD(px, px, px)` call and eight `MONPRO(px, px, px)`
calls, then returns to `ret` with the frame popped. -/
def gasSteps_ccb (s : State) (px : Nat) (ret : UInt256) (rest : List UInt256)
    (mem0 : ByteArray) (mems : Nat → ByteArray)
    (addmod : Challenge.EvmProof.GasSteps (amCallState s mem0 px ret rest)
      (postState s (mems 0) px ret rest))
    (monpro : ∀ i, i < 8 →
      Challenge.EvmProof.GasSteps (mpCallState s (mems i) px (8 - i) ret rest)
        (retState s (mems (i + 1)) px (8 - i) ret rest))
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entryState s mem0 px ret rest)
      (doneState s (mems 8) ret rest) :=
  (((((gasSteps_entry s mem0 px ret rest hcap hcode hfork hrun hnp).trans
    addmod).trans
      (gasSteps_post s (mems 0) px ret rest hcap hcode hfork hrun hnp)).trans
    (gasSteps_loop s px ret rest mems monpro hcap hcode hfork hrun hnp)).trans
      ((gasSteps_call s (mems 7) px 1 ret rest hcap hcode hfork hrun hnp).trans
        (monpro 7 (by omega)))).trans
    ((gasSteps_retLast s (mems 8) px ret rest hcap hcode hfork hrun hnp).trans
      (gasSteps_exit s (mems 8) px ret rest hcap hcode hjump hfork hrun hnp))

end Challenge.Modexp.Submission.Proofs.Fast.Ccb
