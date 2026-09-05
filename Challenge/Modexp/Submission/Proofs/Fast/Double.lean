import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P6
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P7
import Challenge.Modexp.Submission.Proofs.Fast.Csub
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# The `DOUBLE256` subroutine of the appended Montgomery path

`DOUBLE256` occupies instruction indices 1360..1378 (pc 1911..1938).  It is
entered at pc 1911 with stack `[px, ret]` and calls `ADDMOD(px, px, px)` 256
times, so the `n`-limb block at `px` goes from `x` to `x * radix mod m`.

The four basic blocks are

* `blk1360` (idx 1360..1361, pc 1911..1912) — `JUMPDEST; PUSH2 256`;
* `blk1362` (idx 1362..1368, pc 1915..1925) — the loop head `DBL`, which
  pushes the call frame `[px, px, px, 1926]` and jumps to `ADDMOD` (pc 2467);
* `blk1369` (idx 1369..1375, pc 1926..1935) — the return point, which
  decrements the counter and jumps back to pc 1915 while it is nonzero;
* `blk1376` (idx 1376..1378, pc 1936..1938) — `POP; POP; JUMP ret`.

The `ADDMOD` subroutine itself is developed in `Fast.Csub`; here it enters
only through an abstract single-step contract, so this module does not depend
on that development.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Double

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

/-! ## States at the block boundaries

Every state is stated over an arbitrary carrier `s` and overrides only `pc`,
`stack` and `memory`; `activeWords` is carried by `s` and never changes here
because `DOUBLE256` itself contains no memory opcode. -/

/-- The live part of the stack inside the loop: the counter, the block pointer
and the caller's return address. -/
def loopStack (px k : Nat) (ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat k, UInt256.ofNat px, ret] ++ rest

/-- Subroutine entry, pc 1911, stack `[px, ret]`. -/
def entryState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1911
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- The loop head `DBL`, pc 1915, with the counter at `k`. -/
def loopState (s : State) (mem : ByteArray) (px k : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1915
           stack := loopStack px k ret rest
           memory := mem }

/-- The `ADDMOD` call, pc 2467, with the frame `[px, px, px, 1926]` pushed. -/
def callState (s : State) (mem : ByteArray) (px k : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2467
           stack := [UInt256.ofNat px, UInt256.ofNat px, UInt256.ofNat px,
                     UInt256.ofNat 1926] ++ loopStack px k ret rest
           memory := mem }

/-- The return point, pc 1926, with the counter still at `k`. -/
def retState (s : State) (mem : ByteArray) (px k : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1926
           stack := loopStack px k ret rest
           memory := mem }

/-- The loop exit, pc 1936, with the counter at zero. -/
def exitState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1936
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
/-- `blk1360` (pc 1911..1912): the subroutine prologue pushes the counter. -/
theorem run_entry (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1360
      (entryState s mem px ret rest) =
      some (loopState s mem px 256 ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have h256 : (256 : UInt256) = UInt256.ofNat 256 := by decide
  simp (config := { maxSteps := 200000 }) [blk1360, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    entryState, loopState, loopStack, fastPC9, hc2, hrun, h256,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1362` (pc 1915..1925): the loop head pushes the `ADDMOD` frame
`[px, px, px, 1926]` and jumps to pc 2467. -/
theorem run_call (s : State) (mem : ByteArray) (px k : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1362
      (loopState s mem px k ret rest) =
      some (callState s mem px k ret rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have h1926 : (1926 : UInt256) = UInt256.ofNat 1926 := by decide
  have h2467 : (2467 : UInt256) = UInt256.ofNat 2467 := by decide
  have h2467Nat : (UInt256.ofNat 2467).toNat = 2467 := by decide
  simp (config := { maxSteps := 400000 }) [blk1362, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopState, callState, loopStack, fastPC9, hc3, hc4, hc5, hc6, hc7, hc8,
    hcode, hrun,
    h1926, h2467, h2467Nat, jumpDest2467,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1369` (pc 1926..1935), counter above one: decrement and loop. -/
theorem run_ret (s : State) (mem : ByteArray) (px k k' : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hk : k = k' + 1) (hk' : 1 ≤ k') (hk256 : k ≤ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1369
      (retState s mem px k ret rest) =
      some (loopState s mem px k' ret rest) := by
  subst hk
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h1915 : (1915 : UInt256) = UInt256.ofNat 1915 := by decide
  have h1915Nat : (UInt256.ofNat 1915).toNat = 1915 := by decide
  have hsub : UInt256.ofNat (k' + 1) - UInt256.ofNat 1 = UInt256.ofNat k' := by
    have h := Challenge.EvmProof.Word.ofNat_sub_ofNat
      (a := k' + 1) (b := 1) (by omega) (by omega)
    rwa [Nat.add_sub_cancel] at h
  have htrue : UInt256.isTrue (UInt256.ofNat k') := by
    show (UInt256.ofNat k').toNat ≠ 0
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  simp (config := { maxSteps := 400000 }) [blk1369, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    retState, loopState, loopStack, fastPC9, hc3, hc4, hc5, hcode, hrun,
    hone, h1915, h1915Nat, hsub, htrue, jumpDest1915, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1369` (pc 1926..1935), counter one: fall through to the exit. -/
theorem run_retLast (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1369
      (retState s mem px 1 ret rest) =
      some (exitState s mem px ret rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h1915 : (1915 : UInt256) = UInt256.ofNat 1915 := by decide
  have hsub : UInt256.ofNat 1 - UInt256.ofNat 1 = UInt256.ofNat 0 := by decide
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  simp (config := { maxSteps := 400000 }) [blk1369, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    retState, exitState, loopStack, fastPC9, hc3, hc4, hc5, hrun,
    hone, h1915, hsub, hfalse, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1376` (pc 1936..1938): pop the frame and return to the caller. -/
theorem run_exit (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1376
      (exitState s mem px ret rest) =
      some (doneState s mem ret rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  simp (config := { maxSteps := 200000 }) [blk1376, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    exitState, doneState, loopStack, fastPC9, fastPC10, hc1, hc2, hc3, hcode,
    hjump, hrun,
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
      (loopState s mem px 256 ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1360 hcode hfork
      (run_entry s mem px ret rest hcap hrun) hrun hnp

def gasSteps_call (s : State) (mem : ByteArray) (px k : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (loopState s mem px k ret rest)
      (callState s mem px k ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1362 hcode hfork
      (run_call s mem px k ret rest hcap hcode hrun) hrun hnp

def gasSteps_ret (s : State) (mem : ByteArray) (px k k' : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hk : k = k' + 1) (hk' : 1 ≤ k') (hk256 : k ≤ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (retState s mem px k ret rest)
      (loopState s mem px k' ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1369 hcode hfork
      (run_ret s mem px k k' ret rest hcap hk hk' hk256 hcode hrun) hrun hnp

def gasSteps_retLast (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (retState s mem px 1 ret rest)
      (exitState s mem px ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1369 hcode hfork
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
    Artifact.submissionArtifact .Osaka blk1376 hcode hfork
      (run_exit s mem px ret rest hcap hcode hjump hrun) hrun hnp

/-! ## The doubling loop

`ADDMOD` enters here through the indexed contract

```
∀ i < 256, GasSteps (callState s (mems i) px (256 - i) ret rest)
                    (retState s (mems (i + 1)) px (256 - i) ret rest)
```

where `mems i` is the memory after `i` calls.  `Fast.Csub` supplies it; the
instantiation is `gasSteps_double256_addmod` below. -/

/-- `i` applications of a memory transformer. -/
def iterMem (f : ByteArray → ByteArray) (mem : ByteArray) : Nat → ByteArray
  | 0 => mem
  | i + 1 => f (iterMem f mem i)

@[simp] theorem iterMem_zero (f : ByteArray → ByteArray) (mem : ByteArray) :
    iterMem f mem 0 = mem := rfl

theorem iterMem_succ (f : ByteArray → ByteArray) (mem : ByteArray) (i : Nat) :
    iterMem f mem (i + 1) = f (iterMem f mem i) := rfl

/-- The indexed loop-head family: after `i` `ADDMOD` calls the counter stands
at `256 - i`. -/
def loopFamily (s : State) (px : Nat) (ret : UInt256) (rest : List UInt256)
    (mems : Nat → ByteArray) (i : Nat) : State :=
  loopState s (mems i) px (256 - i) ret rest

/-- One loop iteration: call `ADDMOD` and decrement the counter. -/
def gasSteps_iteration (s : State) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (mems : Nat → ByteArray)
    (addmod : ∀ i, i < 256 →
      Challenge.EvmProof.GasSteps (callState s (mems i) px (256 - i) ret rest)
        (retState s (mems (i + 1)) px (256 - i) ret rest))
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (i : Nat) (hi : i < 255) :
    Challenge.EvmProof.GasSteps (loopFamily s px ret rest mems i)
      (loopFamily s px ret rest mems (i + 1)) :=
  ((gasSteps_call s (mems i) px (256 - i) ret rest hcap hcode hfork hrun hnp).trans
      (addmod i (by omega))).trans
    (gasSteps_ret s (mems (i + 1)) px (256 - i) (256 - (i + 1)) ret rest hcap
      (by omega) (by omega) (by omega) hcode hfork hrun hnp)

/-- The 255 iterations that end at the loop head with the counter at one. -/
def gasSteps_loop (s : State) (px : Nat) (ret : UInt256) (rest : List UInt256)
    (mems : Nat → ByteArray)
    (addmod : ∀ i, i < 256 →
      Challenge.EvmProof.GasSteps (callState s (mems i) px (256 - i) ret rest)
        (retState s (mems (i + 1)) px (256 - i) ret rest))
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (loopState s (mems 0) px 256 ret rest)
      (loopState s (mems 255) px 1 ret rest) :=
  Challenge.EvmProof.GasSteps.iterateBounded
    (I := loopFamily s px ret rest mems) 255
    (fun i hi => gasSteps_iteration s px ret rest mems addmod hcap hcode hfork hrun
      hnp i hi)

/-- **Execution certificate for `DOUBLE256`.**  Entering pc 1911 with stack
`[px, ret]` runs 256 `ADDMOD(px, px, px)` calls and returns to `ret` with the
frame popped. -/
def gasSteps_double256 (s : State) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (mems : Nat → ByteArray)
    (addmod : ∀ i, i < 256 →
      Challenge.EvmProof.GasSteps (callState s (mems i) px (256 - i) ret rest)
        (retState s (mems (i + 1)) px (256 - i) ret rest))
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entryState s (mems 0) px ret rest)
      (doneState s (mems 256) ret rest) :=
  ((((gasSteps_entry s (mems 0) px ret rest hcap hcode hfork hrun hnp).trans
    (gasSteps_loop s px ret rest mems addmod hcap hcode hfork hrun hnp)).trans
      ((gasSteps_call s (mems 255) px 1 ret rest hcap hcode hfork hrun hnp).trans
        (addmod 255 (by omega)))).trans
    (gasSteps_retLast s (mems 256) px ret rest hcap hcode hfork hrun hnp)).trans
      (gasSteps_exit s (mems 256) px ret rest hcap hcode hjump hfork hrun hnp)

/-! ## The functional postcondition

`ADDMOD(px, px, px)` doubles the value of the block at `px` modulo `m`; 256
such steps multiply it by `radix`.  Both facts are stated over an abstract
step contract so that they compose with `Fast.Csub.addmod_csub_correct`
without this module depending on it. -/

/-- The doubling invariant: after `i` steps the block at `px` holds
`x * 2 ^ i mod m`. -/
theorem iterMem_represents (f : ByteArray → ByteArray) (mem : ByteArray)
    (px n m x : Nat) (hm : 0 < m)
    (hstep : ∀ (mem' : ByteArray) (y : Nat),
      Model.FastRepresents mem' px n y → y < m →
      Model.FastRepresents (f mem') px n ((y + y) % m))
    (hrep : Model.FastRepresents mem px n x) (hx : x < m) (i : Nat) :
    Model.FastRepresents (iterMem f mem i) px n (Model.doubleChain m x i) := by
  induction i with
  | zero => simpa using hrep
  | succ i ih =>
      rw [iterMem_succ, Model.doubleChain_succ]
      exact hstep _ _ ih (Model.doubleChain_lt hm hx i)

/-- **Functional postcondition of `DOUBLE256`.**  The block at `px` goes from
`x` to `x * radix mod m`. -/
theorem double256_represents (f : ByteArray → ByteArray) (mem : ByteArray)
    (px n m x : Nat) (hm : 0 < m)
    (hstep : ∀ (mem' : ByteArray) (y : Nat),
      Model.FastRepresents mem' px n y → y < m →
      Model.FastRepresents (f mem') px n ((y + y) % m))
    (hrep : Model.FastRepresents mem px n x) (hx : x < m) :
    Model.FastRepresents (iterMem f mem 256) px n (x * Limbs.radix % m) := by
  have h := iterMem_represents f mem px n m x hm hstep hrep hx 256
  rwa [Model.doubleChain_256 hx] at h

/-- The result is still reduced. -/
theorem double256_lt (m x : Nat) (hm : 0 < m) : x * Limbs.radix % m < m :=
  Nat.mod_lt _ hm

/-- **Frame condition.**  Every block the `ADDMOD` step leaves alone survives
all 256 iterations. -/
theorem iterMem_preserves (f : ByteArray → ByteArray) (mem : ByteArray)
    (ptr cnt v : Nat)
    (hpres : ∀ (mem' : ByteArray),
      Model.FastRepresents mem' ptr cnt v → Model.FastRepresents (f mem') ptr cnt v)
    (hrep : Model.FastRepresents mem ptr cnt v) (i : Nat) :
    Model.FastRepresents (iterMem f mem i) ptr cnt v := by
  induction i with
  | zero => simpa using hrep
  | succ i ih => exact hpres _ ih


/-! ## Wiring in the concrete `ADDMOD` subroutine

`Fast.Csub` proves `ADDMOD` from its entry at pc 2467 down to the `CSUB` entry
at pc 2642, and `CSUB` from there to the return jump.  Composing the two gives
the indexed contract the loop above consumes, with memory transformer
`dblStep px n`. -/

/-- The memory one `ADDMOD(px, px, px)` call leaves behind. -/
def dblStep (px n : Nat) (mem : ByteArray) : ByteArray :=
  Csub.csResultMemory (Csub.amResultMemory mem px px n) n px

/-- The three derived variables `ADDMOD` and `CSUB` read: `V_S32 = 0x2480`,
`V_ML = 0x24C0` and `V_TL = 0x24E0`. -/
structure Vars (mem : ByteArray) (n : Nat) : Prop where
  s32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n)
  ml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32)
  tl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n)

theorem loopStack_length (px k : Nat) (ret : UInt256) (rest : List UInt256) :
    (loopStack px k ret rest).length = rest.length + 3 := by
  simp [loopStack]

/-- `ADDMOD` touches nothing at or above `0x2480`. -/
theorem readWord_amResultMemory_high (mem : ByteArray) (pa pb n addr : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (haddr : 9344 ≤ addr) :
    MachineState.readWord (Csub.amResultMemory mem pa pb n) addr =
      MachineState.readWord mem addr := by
  rw [Csub.amResultMemory_def,
    Csub.readWord_write_disjoint _ _ _ _ (Or.inr (by omega)),
    Csub.amStep_readWord_disjoint mem pa pb n addr hn (Or.inr (by omega)) n le_rfl]

/-- `CSUB` touches nothing at or above `0x2480` either, as long as its
destination block stays below. -/
theorem readWord_csResultMemory_high (mem : ByteArray) (n pdst addr : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (hpdst : pdst + 32 * n ≤ 9344) (haddr : 9344 ≤ addr) :
    MachineState.readWord (Csub.csResultMemory mem n pdst) addr =
      MachineState.readWord mem addr := by
  have hsize : (MachineState.readPadded (Csub.csStep mem n n).memory
      (Csub.csSrc mem n n).toNat (32 * n)).size = 32 * n :=
    Challenge.EvmProof.Memory.readPadded_size _ _ _
  simp only [Csub.csResultMemory]
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
      (Or.inr (by rw [hsize]; omega)),
    Csub.csStep_readWord_disjoint mem n addr hn (Or.inr (by omega)) n le_rfl]

theorem vars_dblStep (mem : ByteArray) (px n : Nat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpxFit : px + 32 * n ≤ 8192) (hv : Vars mem n) : Vars (dblStep px n mem) n := by
  refine ⟨?_, ?_, ?_⟩
  · rw [dblStep, readWord_csResultMemory_high _ n px 9344 (by omega) hn32 (by omega)
      (by omega), readWord_amResultMemory_high _ px px n 9344 (by omega) hn32 (by omega)]
    exact hv.s32
  · rw [dblStep, readWord_csResultMemory_high _ n px 9408 (by omega) hn32 (by omega)
      (by omega), readWord_amResultMemory_high _ px px n 9408 (by omega) hn32 (by omega)]
    exact hv.ml
  · rw [dblStep, readWord_csResultMemory_high _ n px 9440 (by omega) hn32 (by omega)
      (by omega), readWord_amResultMemory_high _ px px n 9440 (by omega) hn32 (by omega)]
    exact hv.tl

theorem vars_iterMem (mem : ByteArray) (px n : Nat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpxFit : px + 32 * n ≤ 8192) (hv : Vars mem n) (i : Nat) :
    Vars (iterMem (dblStep px n) mem i) n := by
  induction i with
  | zero => exact hv
  | succ i ih => exact vars_dblStep _ px n hn hn32 hpxFit ih

/-- The `CSUB` return state, spelled as the loop's return state. -/
theorem csReturned_eq (s : State) (mem : ByteArray) (px n k : Nat) (ret : UInt256)
    (rest : List UInt256) (hpx : px < 2 ^ 256) :
    Csub.csReturnedState s (Csub.amResultMemory mem px px n) n n (UInt256.ofNat px)
        (UInt256.ofNat 1926) (loopStack px k ret rest) =
      retState s (dblStep px n mem) px k ret rest := by
  have hpxN : (UInt256.ofNat px).toNat = px := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hpx]
  simp only [Csub.csReturnedState, retState, dblStep, Csub.csResultMemory, hpxN]

/-- One complete `ADDMOD(px, px, px)` call: `ADDMOD` followed by `CSUB`. -/
def gasSteps_addmodStep (s : State) (mem : ByteArray) (px n : Nat) (ret' : UInt256)
    (tail : List UInt256) (hcap : tail.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpx : 32 ≤ px) (hpxFit : px + 32 * n ≤ 8192)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret'.toNat = true)
    (hv : Vars mem n) :
    Challenge.EvmProof.GasSteps
      (Csub.amEntryState s mem px px (UInt256.ofNat px) ret' tail)
      (Csub.csReturnedState s (Csub.amResultMemory mem px px n) n n
        (UInt256.ofNat px) ret' tail) :=
  have hml : MachineState.readWord (Csub.amResultMemory mem px px n) 9408 =
      UInt256.ofNat (32 * n - 32) := by
    rw [readWord_amResultMemory_high _ px px n 9408 (by omega) hn32 (by omega)]
    exact hv.ml
  have htl : MachineState.readWord (Csub.amResultMemory mem px px n) 9440 =
      UInt256.ofNat (8224 + 32 * n) := by
    rw [readWord_amResultMemory_high _ px px n 9440 (by omega) hn32 (by omega)]
    exact hv.tl
  have hs32' : MachineState.readWord
      (Csub.csStep (Csub.amResultMemory mem px px n) n n).memory 9344 =
      UInt256.ofNat (32 * n) := by
    rw [Csub.csStep_readWord_disjoint _ n 9344 (by omega) (Or.inr (by omega)) n le_rfl,
      readWord_amResultMemory_high _ px px n 9344 (by omega) hn32 (by omega)]
    exact hv.s32
  have htn : (MachineState.readWord
      (Csub.csStep (Csub.amResultMemory mem px px n) n n).memory 8224).toNat ≤ 1 := by
    rw [Csub.csStep_readWord_disjoint _ n 8224 (by omega) (Or.inr (by omega)) n le_rfl,
      Csub.addmod_tn]
    exact Csub.addmod_carry_le_one mem px px n hn (by omega) (by omega)
  have hdstFit : (UInt256.ofNat px).toNat + 32 * n ≤ 9472 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (show px ≤ 8192 by omega) (by norm_num))]
    omega
  (Csub.gasSteps_addmod s mem px px n (UInt256.ofNat px) ret' tail hcap hcode hfork hrun
      hnp hact hn hn32 hpx (by omega) hpx (by omega) hv.s32 hv.tl).trans
    (Csub.gasSteps_csub s (Csub.amResultMemory mem px px n) n (UInt256.ofNat px) ret' tail
      hcap hcode hfork hrun hnp hact hn hn32 hjump hml htl hs32' hdstFit htn)

theorem jump1926 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat 1926).toNat = true := by
  rw [show (UInt256.ofNat 1926).toNat = 1926 by decide]
  exact jumpDest1926

/-- **`DOUBLE256` against the real `ADDMOD`.**  With the derived variables in
place, entering pc 1911 with `[px, ret]` returns to `ret` with the block at
`px` doubled 256 times. -/
def gasSteps_double256_addmod (s : State) (mem : ByteArray) (px n : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpx : 32 ≤ px) (hpxFit : px + 32 * n ≤ 8192) (hv : Vars mem n) :
    Challenge.EvmProof.GasSteps (entryState s mem px ret rest)
      (doneState s (iterMem (dblStep px n) mem 256) ret rest) :=
  gasSteps_double256 s px ret rest (iterMem (dblStep px n) mem)
    (fun i _ => Challenge.EvmProof.GasSteps.cast
      (gasSteps_addmodStep s (iterMem (dblStep px n) mem i) px n (UInt256.ofNat 1926)
        (loopStack px (256 - i) ret rest)
        (by rw [loopStack_length]; omega) hcode hfork hrun hnp hact hn hn32 hpx hpxFit
        jump1926 (vars_iterMem mem px n hn hn32 hpxFit hv i))
      rfl
      (csReturned_eq s (iterMem (dblStep px n) mem i) px n (256 - i) ret rest
        (Nat.lt_of_le_of_lt (show px ≤ 8192 by omega) (by norm_num))))
    (by omega) hcode hjump hfork hrun hnp


/-! ## Functional correctness against the concrete `ADDMOD` -/

/-- One `ADDMOD(px, px, px)` call doubles the block at `px` modulo `m`. -/
theorem dblStep_represents (mem : ByteArray) (px n mm x : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hpxFit : px + 32 * n ≤ 8192) (_hpxLow : 32 * n ≤ px)
    (hm : Model.FastRepresents mem 0 n mm) (hmpos : 0 < mm)
    (hx : Model.FastRepresents mem px n x) (hxlt : x < mm) :
    Model.FastRepresents (dblStep px n mem) px n ((x + x) % mm) :=
  Csub.addmod_csub_correct mem px px n x x mm px hn hn32 (by omega) (by omega)
    hx hx hm hmpos (by omega)

/-- One `ADDMOD(px, px, px)` call leaves every block outside the `t`, `SUBB`
and destination areas alone. -/
theorem dblStep_preserves (mem : ByteArray) (px n ptr cnt v : Nat) (hn : 2 ≤ n)
    (hdisjT : ptr + 32 * cnt ≤ 8224 ∨ 8256 + 32 * n ≤ ptr)
    (hdisjSubb : ptr + 32 * cnt ≤ 7168 ∨ 7168 + 32 * n ≤ ptr)
    (hdisjDst : px + 32 * n ≤ ptr ∨ ptr + 32 * cnt ≤ px)
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (dblStep px n mem) ptr cnt v :=
  Csub.addmod_csub_preserves_region mem px px n px ptr cnt v hn hdisjT hdisjSubb
    hdisjDst hrep

/-- **The loop invariant.**  After `i` calls the modulus block is intact and
the block at `px` holds `x * 2 ^ i mod m`. -/
theorem iterMem_dblStep_invariant (mem : ByteArray) (px n mm x : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hpxFit : px + 32 * n ≤ 8192) (hpxLow : 32 * n ≤ px)
    (hmpos : 0 < mm) (hm : Model.FastRepresents mem 0 n mm)
    (hx : Model.FastRepresents mem px n x) (hxlt : x < mm) (i : Nat) :
    Model.FastRepresents (iterMem (dblStep px n) mem i) 0 n mm ∧
      Model.FastRepresents (iterMem (dblStep px n) mem i) px n
        (Model.doubleChain mm x i) := by
  induction i with
  | zero => exact ⟨hm, hx⟩
  | succ i ih =>
      refine ⟨?_, ?_⟩
      · exact dblStep_preserves _ px n 0 n mm hn (by omega) (by omega)
          (Or.inr (by omega)) ih.1
      · rw [iterMem_succ, Model.doubleChain_succ]
        exact dblStep_represents _ px n mm _ hn hn32 hpxFit hpxLow ih.1 hmpos ih.2
          (Model.doubleChain_lt hmpos hxlt i)

/-- **Functional postcondition of `DOUBLE256`.**  The block at `px` goes from
`x` to `x * radix mod m`. -/
theorem double256_addmod_represents (mem : ByteArray) (px n mm x : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hpxFit : px + 32 * n ≤ 8192) (hpxLow : 32 * n ≤ px)
    (hmpos : 0 < mm) (hm : Model.FastRepresents mem 0 n mm)
    (hx : Model.FastRepresents mem px n x) (hxlt : x < mm) :
    Model.FastRepresents (iterMem (dblStep px n) mem 256) px n
      (x * Limbs.radix % mm) := by
  have h := (iterMem_dblStep_invariant mem px n mm x hn hn32 hpxFit hpxLow hmpos hm hx
    hxlt 256).2
  rwa [Model.doubleChain_256 hxlt] at h

/-- The modulus block survives the whole subroutine. -/
theorem double256_addmod_modulus (mem : ByteArray) (px n mm x : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hpxFit : px + 32 * n ≤ 8192) (hpxLow : 32 * n ≤ px)
    (hmpos : 0 < mm) (hm : Model.FastRepresents mem 0 n mm)
    (hx : Model.FastRepresents mem px n x) (hxlt : x < mm) :
    Model.FastRepresents (iterMem (dblStep px n) mem 256) 0 n mm :=
  (iterMem_dblStep_invariant mem px n mm x hn hn32 hpxFit hpxLow hmpos hm hx hxlt 256).1

/-- **Frame condition.**  Every named block outside `T`/`TN`/`TS`, `SUBB` and
`px` itself survives all 256 iterations. -/
theorem double256_addmod_preserves (mem : ByteArray) (px n ptr cnt v : Nat)
    (hn : 2 ≤ n)
    (hdisjT : ptr + 32 * cnt ≤ 8224 ∨ 8256 + 32 * n ≤ ptr)
    (hdisjSubb : ptr + 32 * cnt ≤ 7168 ∨ 7168 + 32 * n ≤ ptr)
    (hdisjDst : px + 32 * n ≤ ptr ∨ ptr + 32 * cnt ≤ px)
    (hrep : Model.FastRepresents mem ptr cnt v) (i : Nat) :
    Model.FastRepresents (iterMem (dblStep px n) mem i) ptr cnt v := by
  induction i with
  | zero => exact hrep
  | succ i ih => exact dblStep_preserves _ px n ptr cnt v hn hdisjT hdisjSubb hdisjDst ih


end Challenge.Modexp.Submission.Proofs.Fast.Double
