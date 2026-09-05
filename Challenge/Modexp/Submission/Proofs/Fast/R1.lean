import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P15
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# The `R1B` guard of the appended Montgomery path

`R1B` occupies instruction indices 1768..1780 (pc 2901..2921).  It is entered
at pc 2901 with stack `[px, ret]`, exactly the calling convention of
`DOUBLE256`, and it dispatches:

* when the modulus's most significant bit is clear it jumps straight to
  `DOUBLE256` (pc 1911) with the stack and memory untouched, so that path is
  literally the old one;
* otherwise it stores `1` at `TN = 0x2020` and jumps to `CSUB` (pc 2642) with
  the same `[px, ret]` frame.

The second branch is the point.  `CSUB` computes `t[n] * radix ^ n + t_low`
reduced against `m`, and at this point in the setup the `t` block at
`TS = 0x2040` is still zero, so with `t[n] = 1` it computes `radix ^ n mod m`
— which is `R mod m`, the value the 256 modular doublings of `DOUBLE256`
produce.  Its side condition `t[n] * radix ^ n + t_low < 2 * m` is exactly the
top-bit guard: a modulus with its most significant bit set satisfies
`radix ^ n < 2 * m`, strictly because `m` is odd and `radix ^ n / 2` is not.

This module depends on `Fast.Csub` only through the value contract
`Csub.csub_correct`; the trace itself is spliced in by the caller.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R1

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

attribute [local simp] List.getElem?_cons_zero

/-! ## The guard -/

/-- The modulus's most significant limb has its top bit set.  This is the
decidable test the block performs with `MLOAD 0; PUSH1 255; SHR`. -/
def TopBitSet (mem : ByteArray) : Prop :=
  2 ^ 255 ≤ (MachineState.readWord mem 0).toNat

instance (mem : ByteArray) : Decidable (TopBitSet mem) := by
  unfold TopBitSet; infer_instance

/-- **The guard is exactly `CSUB`'s side condition.**  If the most significant
limb of an `n`-limb modulus has its top bit set then `radix ^ n < 2 * mm`.
The inequality is strict because `mm` is odd while `radix ^ n / 2` is a power
of two above one. -/
theorem radix_pow_lt_two_mul {mem : ByteArray} {n mm : Nat} (hn : 1 ≤ n)
    (hodd : mm % 2 = 1) (hmod : Model.FastRepresents mem 0 n mm)
    (htop : TopBitSet mem) :
    Limbs.radix ^ n < 2 * mm := by
  have htop' : 2 ^ 255 ≤ (MachineState.readWord mem 0).toNat := htop
  have hlimb : (MachineState.readWord mem 0).toNat =
      mm / Limbs.radix ^ (n - 1) % Limbs.radix := by
    simpa using Model.readWord_of_fastRepresents hmod (j := 0) (by omega)
  -- the modulus's top limb bounds `mm` from below, `% radix` only shrinks it
  have hge : 2 ^ 255 ≤ mm / Limbs.radix ^ (n - 1) :=
    le_trans (hlimb ▸ htop') (Nat.mod_le _ _)
  have hmul : 2 ^ 255 * Limbs.radix ^ (n - 1) ≤ mm :=
    le_trans (Nat.mul_le_mul_right _ hge) (Nat.div_mul_le_self _ _)
  have h2 : (2 : Nat) * 2 ^ 255 = Limbs.radix := by norm_num [Limbs.radix]
  have hhalf : 2 * (2 ^ 255 * Limbs.radix ^ (n - 1)) = Limbs.radix ^ n := by
    rw [← mul_assoc, h2, ← pow_succ']
    congr 1
    omega
  -- `radix ^ n / 2` is even and `mm` is odd, so the bound cannot be tight
  have heven : 2 ^ 255 * Limbs.radix ^ (n - 1) =
      2 * (2 ^ 254 * Limbs.radix ^ (n - 1)) := by
    rw [← mul_assoc]
    congr 1
  omega

/-- `t[n] := 1` at `TN = 0x2020`, the only memory the guard block writes. -/
def tnMem (mem : ByteArray) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 1 32) 8224

/-! ## States at the block boundaries -/

/-- Subroutine entry, pc 2901, stack `[px, ret]`. -/
def entryState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2901
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- The fall-back target, pc 1911: `DOUBLE256`'s own entry, reached with the
stack and memory exactly as they arrived. -/
def dblState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1911
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- Between the test and the store, pc 2912. -/
def fastState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2912
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- The `CSUB` entry, pc 2642, stack `[px, ret]`, with `t[n] = 1` stored.
`TN = 0x2020` lies below the `296` words the caller already holds, so the
store does not grow memory. -/
def csubState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2642
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := tnMem mem }

/-! ## Traces -/

/-- The test falls through when the modulus's top bit is set. -/
theorem run_test_fast (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (_hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) (hact : 296 ≤ s.activeWords.toNat)
    (htop : TopBitSet mem) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1768
      (entryState s mem px ret rest) =
      some (fastState s mem px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hzeroNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hawL : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 0 32) = s.activeWords := by
    have : MachineState.activeWordsAfter s.activeWords.toNat 0 32 =
        s.activeWords.toNat := by
      simp only [MachineState.activeWordsAfter, if_neg (by decide : ¬(32 = 0))]
      exact Nat.max_eq_left (by omega)
    rw [this]
    exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  have hshift : (UInt256.shiftRight (MachineState.readWord mem 0)
      (UInt256.ofNat 255)).toNat = 1 := by
    rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by omega)]
    have hlt : (MachineState.readWord mem 0).toNat < 2 ^ 256 :=
      (MachineState.readWord mem 0).val.isLt
    have := htop
    unfold TopBitSet at this
    simp only [Nat.shiftRight_eq_div_pow]
    omega
  have hcond : (UInt256.shiftRight (MachineState.readWord mem 0)
      (UInt256.ofNat 255)).isZero = UInt256.ofNat 0 := by
    simp only [UInt256.isZero, hshift]
    norm_num
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  simp (config := { maxSteps := 400000 }) [blk1768, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    entryState, fastState, fastPC21, hc2, hc3, hc4, hrun, hcond, hfalse,
    hzeroNat, hawL,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    State.activeWordsAfterUInt256]

/-- The test jumps back to `DOUBLE256` otherwise. -/
theorem run_test_fallback (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) (hact : 296 ≤ s.activeWords.toNat)
    (htop : ¬ TopBitSet mem) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1768
      (entryState s mem px ret rest) =
      some (dblState s mem px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hzeroNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hawL : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 0 32) = s.activeWords := by
    have : MachineState.activeWordsAfter s.activeWords.toNat 0 32 =
        s.activeWords.toNat := by
      simp only [MachineState.activeWordsAfter, if_neg (by decide : ¬(32 = 0))]
      exact Nat.max_eq_left (by omega)
    rw [this]
    exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  have hshift : (UInt256.shiftRight (MachineState.readWord mem 0)
      (UInt256.ofNat 255)).toNat = 0 := by
    rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by omega)]
    unfold TopBitSet at htop
    simp only [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (by omega)
  have hcond : (UInt256.shiftRight (MachineState.readWord mem 0)
      (UInt256.ofNat 255)).isZero = UInt256.ofNat 1 := by
    simp only [UInt256.isZero, hshift]
    norm_num
  have htrue : UInt256.isTrue (UInt256.ofNat 1) := by decide
  simp (config := { maxSteps := 400000 }) [blk1768, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    entryState, dblState, fastPC21, hc2, hc3, hc4, hcode, hrun, hcond, htrue,
    hzeroNat, hawL,
    jumpDest1911,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    State.activeWordsAfterUInt256]

/-- The store and the tail call into `CSUB`. -/
theorem run_fast (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1776
      (fastState s mem px ret rest) =
      some (csubState s mem px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have haw : MachineState.activeWordsAfter s.activeWords.toNat 8224 32 =
      s.activeWords.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : ¬(32 = 0))]
    exact Nat.max_eq_left (by omega)
  have haw' : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 8224 32) =
      s.activeWords := by
    rw [haw]; exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  simp (config := { maxSteps := 400000 }) [blk1776, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    fastState, csubState, tnMem, fastPC21, hc2, hc3, hc4, hcode, hrun,
    jumpDest2642, haw',
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    State.activeWordsAfterUInt256]

end Challenge.Modexp.Submission.Proofs.Fast.R1
