import Challenge.Modexp.Submission.Proofs.Fast.Defs
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P0
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P1
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P6
import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
import Challenge.EvmProof.Memory
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Fast-path entry, precondition checks, fallback and setup

Execution certificate for the head of the appended Montgomery fast path:

* instruction indices 977..1038 — the four precondition checks, which touch no
  memory at all;
* indices 1341..1359 — the three bail blocks, which pop 1, 3 and 6 stack words
  and jump to pc 1196; and
* indices 1039..1136 — the setup block that stores the derived variables,
  loads the modulus into the block at `0x0000`, computes `minv` by eight
  Newton steps and initialises the `R1` block, stopping immediately before the
  first `DOUBLE256` call.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Setup

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

-- Lean 4.31 ships `List.getElem?_cons_zero` without the `simp` attribute, so the
-- program-counter tables of `Fast.Defs` (which end in `[…][i - lo]!`) do not
-- reduce inside the block-reduction `simp` calls without it.
attribute [local simp] List.getElem?_cons_zero

/-! ## Word-level helpers -/

theorem pow_256_32 : (256 : Nat) ^ 32 = 2 ^ 256 := by norm_num

theorem toNat_ofNat_self {a : Nat} (ha : a < 2 ^ 256) :
    (UInt256.ofNat a).toNat = a := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt ha]

theorem gt_ofNat_of_lt {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : b < a) :
    UInt256.gt (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat 1 := by
  rw [UInt256.gt, toNat_ofNat_self ha, toNat_ofNat_self hb, if_pos h]

theorem gt_ofNat_of_le {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : a ≤ b) :
    UInt256.gt (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat 0 := by
  rw [UInt256.gt, toNat_ofNat_self ha, toNat_ofNat_self hb,
    if_neg (Nat.not_lt.mpr h)]

theorem lt_ofNat_of_lt {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : a < b) :
    UInt256.lt (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat 1 := by
  rw [UInt256.lt, toNat_ofNat_self ha, toNat_ofNat_self hb, if_pos h]

theorem lt_ofNat_of_le {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : b ≤ a) :
    UInt256.lt (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat 0 := by
  rw [UInt256.lt, toNat_ofNat_self ha, toNat_ofNat_self hb,
    if_neg (Nat.not_lt.mpr h)]

theorem isZero_ofNat_of_ne {a : Nat} (ha : a < 2 ^ 256) (h : a ≠ 0) :
    UInt256.isZero (UInt256.ofNat a) = UInt256.ofNat 0 := by
  rw [UInt256.isZero, toNat_ofNat_self ha, if_neg h]

theorem isZero_ofNat_zero : UInt256.isZero (UInt256.ofNat 0) = UInt256.ofNat 1 := by
  decide

theorem isZero_ofNat_one : UInt256.isZero (UInt256.ofNat 1) = UInt256.ofNat 0 := by
  decide

@[simp] theorem isTrue_one : UInt256.isTrue (UInt256.ofNat 1) := by decide

@[simp] theorem not_isTrue_zero : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide

@[simp] theorem lor_zero_zero :
    UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by decide

@[simp] theorem lor_zero_one :
    UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 1) = UInt256.ofNat 1 := by decide

@[simp] theorem lor_one_zero :
    UInt256.lor (UInt256.ofNat 1) (UInt256.ofNat 0) = UInt256.ofNat 1 := by decide

@[simp] theorem lor_one_one :
    UInt256.lor (UInt256.ofNat 1) (UInt256.ofNat 1) = UInt256.ofNat 1 := by decide

theorem push0_word : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide

/-! ## Calldata reads and derived geometry -/

theorem initial_code (input : ByteArray) :
    (initialState submissionBytecode input 0).executionEnv.code =
      submissionBytecode := rfl

theorem initial_halt (input : ByteArray) :
    (initialState submissionBytecode input 0).halt = .Running := rfl

theorem read_base (input : ByteArray) :
    MachineState.readWord input 0 = UInt256.ofNat (baseSize input) := rfl

theorem read_exponent (input : ByteArray) :
    MachineState.readWord input 32 = UInt256.ofNat (exponentSize input) := rfl

theorem read_modulus (input : ByteArray) :
    MachineState.readWord input 64 = UInt256.ofNat (modulusSize input) := rfl

theorem headerSize_lt (input : ByteArray) (offset : Nat) :
    Precompile.bytesToNatPadded input offset 32 < 2 ^ 256 := by
  have h := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input offset 32
  rwa [pow_256_32] at h

theorem baseSize_lt (input : ByteArray) : baseSize input < 2 ^ 256 :=
  headerSize_lt input 0

theorem exponentSize_lt (input : ByteArray) : exponentSize input < 2 ^ 256 :=
  headerSize_lt input 32

theorem modulusSize_lt (input : ByteArray) : modulusSize input < 2 ^ 256 :=
  headerSize_lt input 64

/-- `n = ⌈msize / 32⌉`, the number of limbs of the modulus. -/
def limbs (input : ByteArray) : Nat := Limbs.limbCount (modulusSize input)

/-- `s32 = 32 n`, the byte size of every limb block. -/
def s32 (input : ByteArray) : Nat := 32 * limbs input

/-- Calldata offset of the modulus operand. -/
def modOffset (input : ByteArray) : Nat := 96 + baseSize input + exponentSize input

/-- The modulus operand exactly as the specification reads it. -/
def modulus (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input (modOffset input) (modulusSize input)

/-- Byte width of the most significant limb (`1 ≤ topWidth ≤ 32`). -/
def topWidth (input : ByteArray) : Nat := modulusSize input - 32 * (limbs input - 1)

/-- The most significant limb of the modulus, as the top-limb check reads it. -/
def topLimb (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input (modOffset input) (topWidth input)

/-- The fast-path precondition, exactly as indices 977..1038 decide it:
`msize > 32`, all three declared sizes at most 1024, the top limb of the
modulus nonzero, and the modulus odd. -/
def FastPath (input : ByteArray) : Prop :=
  32 < modulusSize input ∧
    (baseSize input ≤ 1024 ∧ exponentSize input ≤ 1024 ∧ modulusSize input ≤ 1024) ∧
    Limbs.radix ^ (limbs input - 1) ≤ modulus input ∧
    modulus input % 2 = 1

theorem limbs_ge_two (input : ByteArray) (h : 32 < modulusSize input) :
    2 ≤ limbs input := by
  unfold limbs Limbs.limbCount
  omega

theorem limbs_le_32 (input : ByteArray) (h : modulusSize input ≤ 1024) :
    limbs input ≤ 32 := by
  unfold limbs Limbs.limbCount
  omega

theorem modulusSize_le_s32 (input : ByteArray) : modulusSize input ≤ s32 input := by
  unfold s32 limbs Limbs.limbCount
  omega

theorem s32_lt_modulusSize_add (input : ByteArray) :
    s32 input < modulusSize input + 32 := by
  unfold s32 limbs Limbs.limbCount
  omega

theorem s32_le_1024 (input : ByteArray) (h : modulusSize input ≤ 1024) :
    s32 input ≤ 1024 := by
  unfold s32 limbs Limbs.limbCount
  omega

theorem topWidth_pos (input : ByteArray) (h : 32 < modulusSize input) :
    0 < topWidth input := by
  unfold topWidth limbs Limbs.limbCount
  omega

theorem topWidth_le (input : ByteArray) : topWidth input ≤ 32 := by
  unfold topWidth limbs Limbs.limbCount
  omega

theorem topWidth_add (input : ByteArray) (h : 32 < modulusSize input) :
    topWidth input + 32 * (limbs input - 1) = modulusSize input := by
  unfold topWidth limbs Limbs.limbCount
  omega


/-! ## States at the check-block boundaries

Block-boundary states are stated over an arbitrary carrier state `s`
constrained only by `s.executionEnv.calldata`, `s.executionEnv.code` and
`s.halt`.  Substituting the concrete `initialState` into the reduction `simp`
calls makes them unfold the frozen bytecode literal, which does not terminate
in reasonable memory. -/

/-- Gas-erased state at the fast-path entry: pc 1314, empty stack. -/
def entryState (s : State) : State :=
  { s with pc := UInt256.ofNat 1314, stack := [] }

/-- The fallback target: pc 1196 with an empty stack; memory and `activeWords`
are untouched because indices 977..1038 and the bail blocks contain no memory
opcode. -/
def fallbackState (s : State) : State :=
  { s with pc := UInt256.ofNat 1196, stack := [] }

/-- Entry of `BAIL1` (pc 1886): one live stack word. -/
def bail1State (s : State) (input : ByteArray) : State :=
  { s with pc := UInt256.ofNat 1886, stack := [UInt256.ofNat (modulusSize input)] }

/-- After the `msize > 32` check (pc 1327). -/
def sizeCheckState (s : State) (input : ByteArray) : State :=
  { s with pc := UInt256.ofNat 1327, stack := [UInt256.ofNat (modulusSize input)] }

set_option linter.unusedSimpArgs false in
theorem run_entry_pass (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input) (hrun : s.halt = .Running)
    (h : 32 < modulusSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk977 (entryState s) =
      some (sizeCheckState s input) := by
  have hgt := gt_ofNat_of_le (by norm_num : (33 : Nat) < 2 ^ 256)
    (modulusSize_lt input) (by omega : 33 ≤ modulusSize input)
  simp (config := { maxSteps := 400000 })
    [blk977, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     entryState, sizeCheckState, hdata, hrun, read_modulus, hgt,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_entry_bail (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running)
    (h : modulusSize input ≤ 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk977 (entryState s) =
      some (bail1State s input) := by
  have hgt := gt_ofNat_of_lt (by norm_num : (33 : Nat) < 2 ^ 256)
    (modulusSize_lt input) (by omega : modulusSize input < 33)
  simp (config := { maxSteps := 400000 })
    [blk977, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     entryState, bail1State, hdata, hcode, hrun, read_modulus, hgt,
     jumpDest1886,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]

/-! ## The three EIP-7823 size bounds -/

theorem ltWord_1024 (a : Nat) (ha : a < 2 ^ 256) :
    UInt256.lt (UInt256.ofNat 1024) (UInt256.ofNat a) =
      UInt256.ofNat (if 1024 < a then 1 else 0) := by
  by_cases hc : 1024 < a
  · rw [if_pos hc, lt_ofNat_of_lt (by norm_num) ha hc]
  · rw [if_neg hc, lt_ofNat_of_le (by norm_num) ha (Nat.not_lt.mp hc)]

/-- The disjunction the size check computes, when every declared size fits. -/
theorem sizeCond_zero (input : ByteArray) (hb : baseSize input ≤ 1024)
    (he : exponentSize input ≤ 1024) (hm : modulusSize input ≤ 1024) :
    UInt256.lor (UInt256.lt (UInt256.ofNat 1024) (UInt256.ofNat (baseSize input)))
        (UInt256.lor (UInt256.lt (UInt256.ofNat 1024) (UInt256.ofNat (exponentSize input)))
          (UInt256.lt (UInt256.ofNat 1024) (UInt256.ofNat (modulusSize input)))) =
      UInt256.ofNat 0 := by
  rw [lt_ofNat_of_le (by norm_num) (baseSize_lt input) hb,
    lt_ofNat_of_le (by norm_num) (exponentSize_lt input) he,
    lt_ofNat_of_le (by norm_num) (modulusSize_lt input) hm, lor_zero_zero,
    lor_zero_zero]

/-- The disjunction the size check computes, when some declared size is too big. -/
theorem sizeCond_one (input : ByteArray)
    (h : 1024 < baseSize input ∨ 1024 < exponentSize input ∨
      1024 < modulusSize input) :
    UInt256.lor (UInt256.lt (UInt256.ofNat 1024) (UInt256.ofNat (baseSize input)))
        (UInt256.lor (UInt256.lt (UInt256.ofNat 1024) (UInt256.ofNat (exponentSize input)))
          (UInt256.lt (UInt256.ofNat 1024) (UInt256.ofNat (modulusSize input)))) =
      UInt256.ofNat 1 := by
  rw [ltWord_1024 _ (baseSize_lt input), ltWord_1024 _ (exponentSize_lt input),
    ltWord_1024 _ (modulusSize_lt input)]
  split_ifs <;> simp_all

/-- After the size checks (pc 1353); also the entry of `BAIL3` at pc 1892. -/
def sizesOkStack (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
   UInt256.ofNat (modulusSize input)]

def topCheckState (s : State) (input : ByteArray) : State :=
  { s with pc := UInt256.ofNat 1353, stack := sizesOkStack input }

def bail3State (s : State) (input : ByteArray) : State :=
  { s with pc := UInt256.ofNat 1892, stack := sizesOkStack input }

set_option linter.unusedSimpArgs false in
theorem run_sizeCheck_pass (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input) (hrun : s.halt = .Running)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk986 (sizeCheckState s input) =
      some (topCheckState s input) := by
  have hcond := sizeCond_zero input hb he hm
  simp (config := { maxSteps := 400000 })
    [blk986, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     sizeCheckState, topCheckState, sizesOkStack, hdata, hrun, push0_word,
     read_base, read_exponent, hcond,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_sizeCheck_bail (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running)
    (h : 1024 < baseSize input ∨ 1024 < exponentSize input ∨
      1024 < modulusSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk986 (sizeCheckState s input) =
      some (bail3State s input) := by
  have hcond := sizeCond_one input h
  simp (config := { maxSteps := 400000 })
    [blk986, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     sizeCheckState, bail3State, sizesOkStack, hdata, hcode, hrun, push0_word,
     read_base, read_exponent, hcond, jumpDest1892,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]

/-! ## Word arithmetic of the top-limb block -/

/-- `2 ^ 256` spelled the way `simp` normalises it, so that the residual
`% 2 ^ 256` produced by `word_toNat_ofNat` can be discharged by rewriting. -/
theorem mod_word_self {a : Nat} (h : a < 2 ^ 256) :
    a % 115792089237316195423570985008687907853269984665640564039457584007913129639936
      = a :=
  Nat.mod_eq_of_lt h

theorem limbs_lt (input : ByteArray) (hm : modulusSize input ≤ 1024) :
    limbs input < 2 ^ 256 := by
  have h := limbs_le_32 input hm
  omega

theorem s32_lt (input : ByteArray) (hm : modulusSize input ≤ 1024) :
    s32 input < 2 ^ 256 := by
  have h := s32_le_1024 input hm
  omega

theorem modOffset_lt (input : ByteArray) (hb : baseSize input ≤ 1024)
    (he : exponentSize input ≤ 1024) : modOffset input < 2 ^ 256 := by
  unfold modOffset
  omega

theorem shr5_limbs (input : ByteArray) (hm : modulusSize input ≤ 1024) :
    UInt256.shiftRight (UInt256.ofNat (31 + modulusSize input)) (UInt256.ofNat 5) =
      UInt256.ofNat (limbs input) := by
  have h31 : 31 + modulusSize input < 2 ^ 256 := by omega
  rw [Challenge.EvmProof.Word.shiftRight_ofNat h31 (by norm_num)]
  congr 1
  rw [Nat.shiftRight_eq_div_pow]
  unfold limbs Limbs.limbCount
  norm_num
  omega

theorem shl5_s32 (input : ByteArray) (hm : modulusSize input ≤ 1024) :
    UInt256.shiftLeft (UInt256.ofNat (limbs input)) (UInt256.ofNat 5) =
      UInt256.ofNat (s32 input) := by
  have hn := limbs_le_32 input hm
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (limbs_lt input hm) (by norm_num)
    (by norm_num; omega)]
  congr 1
  unfold s32
  norm_num
  omega

theorem sub_s32_msize (input : ByteArray) (hm : modulusSize input ≤ 1024) :
    UInt256.ofNat (s32 input) - UInt256.ofNat (modulusSize input) =
      UInt256.ofNat (s32 input - modulusSize input) :=
  Challenge.EvmProof.Word.ofNat_sub_ofNat (modulusSize_le_s32 input) (s32_lt input hm)

theorem shl3_shift (input : ByteArray) (hm : modulusSize input ≤ 1024) :
    UInt256.shiftLeft (UInt256.ofNat (s32 input - modulusSize input))
        (UInt256.ofNat 3) =
      UInt256.ofNat ((s32 input - modulusSize input) * 8) := by
  have hs := s32_le_1024 input hm
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by norm_num)
    (by norm_num; omega)]
  norm_num

theorem topLimb_lt (input : ByteArray) : topLimb input < 2 ^ 256 := by
  have h := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input (modOffset input)
    (topWidth input)
  have hle : 256 ^ topWidth input ≤ 256 ^ 32 :=
    Nat.pow_le_pow_right (by norm_num) (topWidth_le input)
  rw [pow_256_32] at hle
  exact h.trans_le hle

/-- The right shift performed by the top-limb check extracts the most
significant limb of the modulus. -/
theorem shiftRight_topLimb (input : ByteArray) (h : 32 < modulusSize input) :
    UInt256.shiftRight (MachineState.readWord input (modOffset input))
        (UInt256.ofNat ((s32 input - modulusSize input) * 8)) =
      UInt256.ofNat (topLimb input) := by
  have hshift : (s32 input - modulusSize input) * 8 = (32 - topWidth input) * 8 := by
    unfold s32 topWidth limbs Limbs.limbCount
    omega
  rw [hshift]
  exact Challenge.EvmProof.Bytes.shiftRight_readWord input (modOffset input)
    (topWidth input) (topWidth_pos input h) (topWidth_le input)

/-! ## The top-limb check -/

/-- `OUTER = [s32, n, bsize, esize, msize]`, the stack bottom the whole fast
path keeps live. -/
def outerStack (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat (s32 input), UInt256.ofNat (limbs input),
   UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
   UInt256.ofNat (modulusSize input)]

/-- After the top-limb check (pc 1385). -/
def oddCheckState (s : State) (input : ByteArray) : State :=
  { s with pc := UInt256.ofNat 1385
           stack := UInt256.ofNat (modOffset input) :: outerStack input }

/-- Entry of `BAIL6` (pc 1900): six live stack words. -/
def bail6State (s : State) (input : ByteArray) : State :=
  { s with pc := UInt256.ofNat 1900
           stack := UInt256.ofNat (modOffset input) :: outerStack input }

set_option linter.unusedSimpArgs false in
theorem run_topCheck_pass (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input) (hrun : s.halt = .Running)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input)
    (htop : topLimb input ≠ 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1003 (topCheckState s input) =
      some (oddCheckState s input) := by
  have hmoff : 96 + (baseSize input + exponentSize input) = modOffset input := by
    unfold modOffset; omega
  have hmodmod := mod_word_self (modOffset_lt input hb he)
  have hzero := isZero_ofNat_of_ne (topLimb_lt input) htop
  simp (config := { maxSteps := 800000 })
    [blk1003, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     topCheckState, oddCheckState, sizesOkStack, outerStack, hdata, hrun,
     shr5_limbs input hm, shl5_s32 input hm, sub_s32_msize input hm,
     shl3_shift input hm, hmoff, hmodmod, shiftRight_topLimb input h32, hzero,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_topCheck_bail (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input)
    (htop : topLimb input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1003 (topCheckState s input) =
      some (bail6State s input) := by
  have hmoff : 96 + (baseSize input + exponentSize input) = modOffset input := by
    unfold modOffset; omega
  have hmodmod := mod_word_self (modOffset_lt input hb he)
  simp (config := { maxSteps := 800000 })
    [blk1003, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     topCheckState, bail6State, sizesOkStack, outerStack, hdata, hcode, hrun,
     shr5_limbs input hm, shl5_s32 input hm, sub_s32_msize input hm,
     shl3_shift input hm, hmoff, hmodmod, shiftRight_topLimb input h32, htop,
     isZero_ofNat_zero, jumpDest1900,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange]

/-! ## The parity check -/

/-- The parity of the modulus is the low bit of its last calldata word. -/
theorem land_one_lastWord (input : ByteArray) (h : 32 < modulusSize input) :
    UInt256.land (UInt256.ofNat 1)
        (MachineState.readWord input (modOffset input + modulusSize input - 32)) =
      UInt256.ofNat (modulus input % 2) := by
  have h1 : (UInt256.ofNat 1).toNat = 1 := by decide
  have h2 : (UInt256.ofNat (modulus input % 2)).toNat = modulus input % 2 :=
    toNat_ofNat_self (by omega)
  have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add input (modOffset input)
    (modulusSize input - 32) 32
  rw [show modulusSize input - 32 + 32 = modulusSize input from by omega] at hsplit
  have haddr : modOffset input + modulusSize input - 32 =
      modOffset input + (modulusSize input - 32) := by omega
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land, h1, h2,
    Challenge.EvmProof.Bytes.readWord_toNat, Nat.one_and_eq_mod_two, haddr]
  unfold modulus
  rw [hsplit, Nat.add_mod, Nat.mul_mod, show (256:Nat) ^ 32 % 2 = 0 from by norm_num]
  simp

/-- State after all four checks passed (pc 1400), before any memory write. -/
def setupEntryState (s : State) (input : ByteArray) : State :=
  { s with pc := UInt256.ofNat 1400
           stack := UInt256.ofNat (modOffset input) :: outerStack input }

set_option linter.unusedSimpArgs false in
theorem run_oddCheck_pass (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input) (hrun : s.halt = .Running)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input)
    (hodd : modulus input % 2 = 1) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1028 (oddCheckState s input) =
      some (setupEntryState s input) := by
  have hmoffval : modOffset input = 96 + baseSize input + exponentSize input := rfl
  have hsub : UInt256.ofNat (modOffset input + modulusSize input) - UInt256.ofNat 32 =
      UInt256.ofNat (modOffset input + modulusSize input - 32) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)
  have hmodmod := mod_word_self
    (show modOffset input + modulusSize input - 32 < 2 ^ 256 by omega)
  simp (config := { maxSteps := 800000 })
    [blk1028, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     oddCheckState, setupEntryState, outerStack, hdata, hrun, hsub, hmodmod,
     land_one_lastWord input h32, hodd, isZero_ofNat_one,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_oddCheck_bail (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input)
    (hodd : modulus input % 2 = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1028 (oddCheckState s input) =
      some (bail6State s input) := by
  have hmoffval : modOffset input = 96 + baseSize input + exponentSize input := rfl
  have hsub : UInt256.ofNat (modOffset input + modulusSize input) - UInt256.ofNat 32 =
      UInt256.ofNat (modOffset input + modulusSize input - 32) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)
  have hmodmod := mod_word_self
    (show modOffset input + modulusSize input - 32 < 2 ^ 256 by omega)
  simp (config := { maxSteps := 800000 })
    [blk1028, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     oddCheckState, bail6State, outerStack, hdata, hcode, hrun, hsub, hmodmod,
     land_one_lastWord input h32, hodd, isZero_ofNat_zero, jumpDest1900,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]

/-! ## The three bail blocks

Each drops its live stack words and jumps to pc 1196.  No instruction between
index 977 and any of these blocks is `MSTORE`, `MSTORE8`, `MCOPY` or
`CALLDATACOPY`, so memory and `activeWords` are still those of `s`. -/

set_option linter.unusedSimpArgs false in
theorem run_bail1 (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1341 (bail1State s input) =
      some (fallbackState s) := by
  simp (config := { maxSteps := 400000 })
    [blk1341, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     bail1State, fallbackState, hcode, hrun, jumpDest1196,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_bail3 (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1345 (bail3State s input) =
      some (fallbackState s) := by
  simp (config := { maxSteps := 400000 })
    [blk1345, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     bail3State, sizesOkStack, fallbackState, hcode, hrun, jumpDest1196,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_bail6 (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1351 (bail6State s input) =
      some (fallbackState s) := by
  simp (config := { maxSteps := 400000 })
    [blk1351, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     bail6State, outerStack, fallbackState, hcode, hrun, jumpDest1196,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]

/-! ## The top-limb check decides `radix ^ (n - 1) ≤ m` -/

theorem modulus_lt (input : ByteArray) :
    modulus input < Limbs.radix ^ limbs input :=
  Limbs.byteValue_fits_limbs input (modOffset input) (modulusSize input)

/-- The modulus splits into its top limb and a tail below `radix ^ (n - 1)`. -/
theorem modulus_split (input : ByteArray) (h : 32 < modulusSize input) :
    modulus input = topLimb input * Limbs.radix ^ (limbs input - 1) +
      Precompile.bytesToNatPadded input (modOffset input + topWidth input)
        (32 * (limbs input - 1)) := by
  unfold modulus topLimb
  rw [← topWidth_add input h, Challenge.EvmProof.Bytes.bytesToNatPadded_add,
    Limbs.pow_radix]

theorem modulus_tail_lt (input : ByteArray) :
    Precompile.bytesToNatPadded input (modOffset input + topWidth input)
        (32 * (limbs input - 1)) < Limbs.radix ^ (limbs input - 1) := by
  rw [Limbs.pow_radix]
  exact Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow _ _ _

/-- The check the code performs (`topLimb ≠ 0`) is the arithmetic statement
`radix ^ (n - 1) ≤ m`. -/
theorem topLimb_ne_zero_iff (input : ByteArray) (h : 32 < modulusSize input) :
    topLimb input ≠ 0 ↔ Limbs.radix ^ (limbs input - 1) ≤ modulus input := by
  have hsplit := modulus_split input h
  have htail := modulus_tail_lt input
  constructor
  · intro hne
    have hone : 1 ≤ topLimb input := Nat.one_le_iff_ne_zero.mpr hne
    rw [hsplit]
    calc Limbs.radix ^ (limbs input - 1)
        = 1 * Limbs.radix ^ (limbs input - 1) := (Nat.one_mul _).symm
      _ ≤ topLimb input * Limbs.radix ^ (limbs input - 1) :=
          Nat.mul_le_mul_right _ hone
      _ ≤ _ := Nat.le_add_right _ _
  · intro hle hzero
    rw [hsplit, hzero, Nat.zero_mul, Nat.zero_add] at hle
    omega

/-! ## Gas traces for the individual blocks -/

def gasSteps_entry_pass (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (h : 32 < modulusSize input) :
    Challenge.EvmProof.GasSteps (entryState s) (sizeCheckState s input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk977 hcode hfork
      (run_entry_pass s input hdata hrun h) hrun hnp

def gasSteps_entry_bail (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (h : modulusSize input ≤ 32) :
    Challenge.EvmProof.GasSteps (entryState s) (bail1State s input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk977 hcode hfork
      (run_entry_bail s input hdata hcode hrun h) hrun hnp

def gasSteps_sizeCheck_pass (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) :
    Challenge.EvmProof.GasSteps (sizeCheckState s input) (topCheckState s input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk986 hcode hfork
      (run_sizeCheck_pass s input hdata hrun hb he hm) hrun hnp

def gasSteps_sizeCheck_bail (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (h : 1024 < baseSize input ∨ 1024 < exponentSize input ∨
      1024 < modulusSize input) :
    Challenge.EvmProof.GasSteps (sizeCheckState s input) (bail3State s input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk986 hcode hfork
      (run_sizeCheck_bail s input hdata hcode hrun h) hrun hnp

def gasSteps_topCheck_pass (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input)
    (htop : topLimb input ≠ 0) :
    Challenge.EvmProof.GasSteps (topCheckState s input) (oddCheckState s input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1003 hcode hfork
      (run_topCheck_pass s input hdata hrun hb he hm h32 htop) hrun hnp

def gasSteps_topCheck_bail (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input)
    (htop : topLimb input = 0) :
    Challenge.EvmProof.GasSteps (topCheckState s input) (bail6State s input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1003 hcode hfork
      (run_topCheck_bail s input hdata hcode hrun hb he hm h32 htop) hrun hnp

def gasSteps_oddCheck_pass (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input)
    (hodd : modulus input % 2 = 1) :
    Challenge.EvmProof.GasSteps (oddCheckState s input) (setupEntryState s input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1028 hcode hfork
      (run_oddCheck_pass s input hdata hrun hb he hm h32 hodd) hrun hnp

def gasSteps_oddCheck_bail (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input)
    (hodd : modulus input % 2 = 0) :
    Challenge.EvmProof.GasSteps (oddCheckState s input) (bail6State s input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1028 hcode hfork
      (run_oddCheck_bail s input hdata hcode hrun hb he hm h32 hodd) hrun hnp

def gasSteps_bail1 (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (bail1State s input) (fallbackState s) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1341 hcode hfork
      (run_bail1 s input hcode hrun) hrun hnp

def gasSteps_bail3 (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (bail3State s input) (fallbackState s) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1345 hcode hfork
      (run_bail3 s input hcode hrun) hrun hnp

def gasSteps_bail6 (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (bail6State s input) (fallbackState s) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1351 hcode hfork
      (run_bail6 s input hcode hrun) hrun hnp

/-! ## The fallback trace

Every calldata that fails the fast-path precondition reaches pc 1196 with an
empty stack and untouched memory. -/

def gasSteps_fallback_of (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hfail : ¬ FastPath input) :
    Challenge.EvmProof.GasSteps (entryState s) (fallbackState s) :=
  if h1 : 32 < modulusSize input then
    if hb : baseSize input ≤ 1024 then
      if he : exponentSize input ≤ 1024 then
        if hm : modulusSize input ≤ 1024 then
          if htop : topLimb input = 0 then
            (gasSteps_entry_pass s input hdata hcode hfork hrun hnp h1).trans
              ((gasSteps_sizeCheck_pass s input hdata hcode hfork hrun hnp hb he hm).trans
                ((gasSteps_topCheck_bail s input hdata hcode hfork hrun hnp
                    hb he hm h1 htop).trans
                  (gasSteps_bail6 s input hcode hfork hrun hnp)))
          else
            if hodd : modulus input % 2 = 0 then
              (gasSteps_entry_pass s input hdata hcode hfork hrun hnp h1).trans
                ((gasSteps_sizeCheck_pass s input hdata hcode hfork hrun hnp hb he hm).trans
                  ((gasSteps_topCheck_pass s input hdata hcode hfork hrun hnp
                      hb he hm h1 htop).trans
                    ((gasSteps_oddCheck_bail s input hdata hcode hfork hrun hnp
                        hb he hm h1 hodd).trans
                      (gasSteps_bail6 s input hcode hfork hrun hnp))))
            else
              absurd (show FastPath input from
                ⟨h1, ⟨hb, he, hm⟩, (topLimb_ne_zero_iff input h1).mp htop, by omega⟩)
                hfail
        else
          (gasSteps_entry_pass s input hdata hcode hfork hrun hnp h1).trans
            ((gasSteps_sizeCheck_bail s input hdata hcode hfork hrun hnp
                (Or.inr (Or.inr (by omega)))).trans
              (gasSteps_bail3 s input hcode hfork hrun hnp))
      else
        (gasSteps_entry_pass s input hdata hcode hfork hrun hnp h1).trans
          ((gasSteps_sizeCheck_bail s input hdata hcode hfork hrun hnp
              (Or.inr (Or.inl (by omega)))).trans
            (gasSteps_bail3 s input hcode hfork hrun hnp))
    else
      (gasSteps_entry_pass s input hdata hcode hfork hrun hnp h1).trans
        ((gasSteps_sizeCheck_bail s input hdata hcode hfork hrun hnp
            (Or.inl (by omega))).trans
          (gasSteps_bail3 s input hcode hfork hrun hnp))
  else
    (gasSteps_entry_bail s input hdata hcode hfork hrun hnp (by omega)).trans
      (gasSteps_bail1 s input hcode hfork hrun hnp)

theorem entryState_initial (input : ByteArray) :
    entryState (initialState submissionBytecode input 0) =
      Main.trampolineState input 1314 := rfl

theorem fallbackState_initial (input : ByteArray) :
    fallbackState (initialState submissionBytecode input 0) =
      Main.trampolineState input 1196 := rfl

/-- **Fallback certificate.**  For every calldata failing the fast-path
precondition, the appended entry block runs from the state the retargeted
entry `PUSH2 1314; JUMP` produces to `Main.trampolineState input 1196` — pc
1196, empty stack, untouched memory and `activeWords` — which is exactly the
state the pre-existing reference proof consumes. -/
def gasSteps_fallback (input : ByteArray) (hfail : ¬ FastPath input) :
    Challenge.EvmProof.GasSteps (Main.trampolineState input 1314)
      (Main.trampolineState input 1196) :=
  Challenge.EvmProof.GasSteps.cast
    (gasSteps_fallback_of (initialState submissionBytecode input 0) input rfl rfl rfl rfl
      deployAddress_not_precompile hfail)
    (entryState_initial input) (fallbackState_initial input)

/-! ## Wrapping word arithmetic for the Newton iteration -/

theorem word_toNat_mul (a b : UInt256) :
    (a * b).toNat = a.toNat * b.toNat % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl

theorem ofNat_congr_mod {a b : Nat} (h : a % 2 ^ 256 = b % 2 ^ 256) :
    UInt256.ofNat a = UInt256.ofNat b := by
  apply Challenge.EvmProof.Word.word_ext
  simpa using h

theorem ofNat_mul_mod (a b : Nat) :
    UInt256.ofNat a * UInt256.ofNat b = UInt256.ofNat (a * b) := by
  apply Challenge.EvmProof.Word.word_ext
  simp only [word_toNat_mul, Challenge.EvmProof.Word.word_toNat_ofNat, ← Nat.mul_mod]

theorem ofNat_sub_word (a b : Nat) :
    UInt256.ofNat a - UInt256.ofNat b =
      UInt256.ofNat (2 ^ 256 + a % 2 ^ 256 - b % 2 ^ 256) := by
  apply Challenge.EvmProof.Word.word_ext
  simp only [Challenge.EvmProof.Word.word_toNat_sub,
    Challenge.EvmProof.Word.word_toNat_ofNat]

/-- One `DUP1; DUP3; MUL; PUSH1 2; SUB; MUL` group is one Newton step. -/
theorem newton_word_step (m0 x : Nat) :
    (UInt256.ofNat 2 - UInt256.ofNat m0 * UInt256.ofNat x) * UInt256.ofNat x =
      UInt256.ofNat (Model.newtonStep m0 x) := by
  have h2 : (2 : Nat) % 2 ^ 256 = 2 := by norm_num
  have hr : Limbs.radix = 2 ^ 256 := rfl
  have hcong : x * ((2 + 2 ^ 256 - m0 * x % 2 ^ 256) % 2 ^ 256) % 2 ^ 256
      = x * (2 + 2 ^ 256 - m0 * x % 2 ^ 256) % 2 ^ 256 :=
    (Nat.mod_modEq (2 + 2 ^ 256 - m0 * x % 2 ^ 256) (2 ^ 256)).mul_left x
  rw [ofNat_mul_mod, ofNat_sub_word, ofNat_mul_mod]
  apply ofNat_congr_mod
  rw [h2]
  unfold Model.newtonStep
  rw [hr, Nat.mod_mod_of_dvd _ (dvd_refl (2 ^ 256)), hcong, Nat.mul_comm x,
    Nat.add_comm 2 (2 ^ 256)]

/-! ## The setup block

Instructions 1039..1137 (pc 1400..1532) are one straight-line basic block: the
five derived variables, the two `CALLDATACOPY`s that place the modulus
right-aligned in the `n`-limb block at `0x0000`, the eight Newton steps that
compute `minv`, the `R1` initialisation and the jump into `DOUBLE256`.  It is
reduced in four pieces so that no single `simp` call has to normalise ninety-
nine instructions at once. -/

/-- `-v mod 2^256`, the value the `PUSH0; SUB` before `MSTORE V_MINV` leaves. -/
def negWord (v : Nat) : Nat := (Limbs.radix - v % Limbs.radix) % Limbs.radix

theorem negWord_lt (v : Nat) : negWord v < 2 ^ 256 :=
  Nat.mod_lt _ Limbs.radix_pos

theorem neg_word (v : Nat) :
    UInt256.ofNat 0 - UInt256.ofNat v = UInt256.ofNat (negWord v) := by
  rw [ofNat_sub_word]
  apply ofNat_congr_mod
  unfold negWord Limbs.radix
  rw [Nat.mod_mod_of_dvd _ (dvd_refl (2 ^ 256))]
  congr 1

/-- The first four Newton steps. -/
def newton4 (m0 : Nat) : Nat :=
  Model.newtonStep m0 (Model.newtonStep m0 (Model.newtonStep m0
    (Model.newtonStep m0 1)))

/-- All eight Newton steps. -/
def newton8 (m0 : Nat) : Nat :=
  Model.newtonStep m0 (Model.newtonStep m0 (Model.newtonStep m0
    (Model.newtonStep m0 (newton4 m0))))

theorem newton8_eq (m0 : Nat) : newton8 m0 = Model.newtonIter m0 8 := rfl

/-- One `MSTORE` of a natural-number value. -/
def mstoreAt (mem : ByteArray) (addr value : Nat) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded value 32) addr

/-- Memory after the five variable stores. -/
def varsMem (mem : ByteArray) (input : ByteArray) : ByteArray :=
  mstoreAt (mstoreAt (mstoreAt (mstoreAt (mstoreAt mem 9344 (s32 input))
    9504 (limbs input)) 9472 (96 + baseSize input)) 9408 (s32 input - 32))
    9440 (8224 + s32 input)

/-- Memory after the two `CALLDATACOPY`s: the block at `0x0000` is zeroed and
the `msize` modulus bytes are then written right-aligned into it. -/
def modulusMem (mem : ByteArray) (input : ByteArray) : ByteArray :=
  MachineState.writeBytes
    (MachineState.writeBytes (varsMem mem input)
      (MachineState.readPadded input input.size (s32 input)) 0)
    (MachineState.readPadded input (modOffset input) (modulusSize input))
    (s32 input - modulusSize input)

/-- Memory at the end of the setup block. -/
def setupMem (mem : ByteArray) (input : ByteArray) (m0 : Nat) : ByteArray :=
  mstoreAt (mstoreAt (modulusMem mem input) 9376 (negWord (newton8 m0))) 4096 1

/-- One memory-expansion step, with the word wrapping the machine performs. -/
def awNext (w off sz : Nat) : Nat :=
  MachineState.activeWordsAfter (w % 2 ^ 256) off sz

/-- `activeWords` after the variable stores, the copies and the `MLOAD`. -/
def loadWords (w : UInt256) (input : ByteArray) : UInt256 :=
  UInt256.ofNat (awNext (awNext (awNext (awNext (awNext (awNext (awNext
    (MachineState.activeWordsAfter w.toNat 9344 32) 9504 32) 9472 32) 9408 32)
    9440 32) 0 (s32 input)) (s32 input - modulusSize input) (modulusSize input))
    (s32 input - 32) 32)

/-- `activeWords` at the end of the setup block. -/
def setupWords (w : UInt256) (input : ByteArray) : UInt256 :=
  UInt256.ofNat (awNext
    (MachineState.activeWordsAfter (loadWords w input).toNat 9376 32) 4096 32)

/-- Instructions 1039..1075: the variables, the modulus copies and the
`MLOAD` of its least significant limb. -/
def setupPathA :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1039 (.Dup ⟨1, by decide⟩), pushAt 1040 2 9344, opAt 1041 .MSTORE,
   opAt 1042 (.Dup ⟨2, by decide⟩), pushAt 1043 2 9504, opAt 1044 .MSTORE,
   opAt 1045 (.Dup ⟨3, by decide⟩), pushAt 1046 1 96, opAt 1047 .ADD,
   pushAt 1048 2 9472, opAt 1049 .MSTORE, opAt 1050 (.Dup ⟨1, by decide⟩),
   pushAt 1051 1 32, opAt 1052 (.Swap ⟨0, by decide⟩), opAt 1053 .SUB,
   opAt 1054 (.Dup ⟨0, by decide⟩), pushAt 1055 2 9408, opAt 1056 .MSTORE,
   opAt 1057 (.Dup ⟨2, by decide⟩), pushAt 1058 2 8224, opAt 1059 .ADD,
   pushAt 1060 2 9440, opAt 1061 .MSTORE, opAt 1062 (.Dup ⟨2, by decide⟩),
   opAt 1063 .CALLDATASIZE, pushAt 1064 0 0, opAt 1065 .CALLDATACOPY,
   opAt 1066 (.Dup ⟨6, by decide⟩), opAt 1067 (.Dup ⟨2, by decide⟩),
   opAt 1068 (.Dup ⟨1, by decide⟩), opAt 1069 (.Dup ⟨5, by decide⟩),
   opAt 1070 .SUB, opAt 1071 .CALLDATACOPY,
   opAt 1072 (.Swap ⟨0, by decide⟩), opAt 1073 .POP,
   opAt 1074 (.Dup ⟨0, by decide⟩), opAt 1075 .MLOAD]

/-- Instructions 1076..1100: `x := 1` and the first four Newton steps. -/
def setupPathB :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1076 1 1, opAt 1077 (.Dup ⟨0, by decide⟩),
   opAt 1078 (.Dup ⟨2, by decide⟩), opAt 1079 .MUL, pushAt 1080 1 2,
   opAt 1081 .SUB, opAt 1082 .MUL, opAt 1083 (.Dup ⟨0, by decide⟩),
   opAt 1084 (.Dup ⟨2, by decide⟩), opAt 1085 .MUL, pushAt 1086 1 2,
   opAt 1087 .SUB, opAt 1088 .MUL, opAt 1089 (.Dup ⟨0, by decide⟩),
   opAt 1090 (.Dup ⟨2, by decide⟩), opAt 1091 .MUL, pushAt 1092 1 2,
   opAt 1093 .SUB, opAt 1094 .MUL, opAt 1095 (.Dup ⟨0, by decide⟩),
   opAt 1096 (.Dup ⟨2, by decide⟩), opAt 1097 .MUL, pushAt 1098 1 2,
   opAt 1099 .SUB, opAt 1100 .MUL]

/-- Instructions 1101..1124: the last four Newton steps. -/
def setupPathC :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1101 (.Dup ⟨0, by decide⟩), opAt 1102 (.Dup ⟨2, by decide⟩),
   opAt 1103 .MUL, pushAt 1104 1 2, opAt 1105 .SUB, opAt 1106 .MUL,
   opAt 1107 (.Dup ⟨0, by decide⟩), opAt 1108 (.Dup ⟨2, by decide⟩),
   opAt 1109 .MUL, pushAt 1110 1 2, opAt 1111 .SUB, opAt 1112 .MUL,
   opAt 1113 (.Dup ⟨0, by decide⟩), opAt 1114 (.Dup ⟨2, by decide⟩),
   opAt 1115 .MUL, pushAt 1116 1 2, opAt 1117 .SUB, opAt 1118 .MUL,
   opAt 1119 (.Dup ⟨0, by decide⟩), opAt 1120 (.Dup ⟨2, by decide⟩),
   opAt 1121 .MUL, pushAt 1122 1 2, opAt 1123 .SUB, opAt 1124 .MUL]

/-- Instructions 1125..1137: `MSTORE V_MINV`, `MSTORE R1 1` and the tail call
into the `R1B` guard. -/
def setupPathD :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1125 0 0, opAt 1126 .SUB, pushAt 1127 2 9376, opAt 1128 .MSTORE,
   opAt 1129 .POP, opAt 1130 .POP, pushAt 1131 1 1, pushAt 1132 2 4096,
   opAt 1133 .MSTORE, pushAt 1134 2 1533, pushAt 1135 2 4096,
   pushAt 1136 2 2901, opAt 1137 .JUMP]

/-- After the variable stores and the modulus load (pc 1451). -/
def modLoadedState (s : State) (input : ByteArray) (m0 : Nat) : State :=
  { s with pc := UInt256.ofNat 1451
           stack := UInt256.ofNat m0 :: UInt256.ofNat (s32 input - 32) ::
             outerStack input
           memory := modulusMem s.memory input
           activeWords := loadWords s.activeWords input }

/-- Inside the Newton chain: `x` on top of `m0` and the outer frame. -/
def newtonState (s : State) (input : ByteArray) (m0 x p : Nat) : State :=
  { s with pc := UInt256.ofNat p
           stack := UInt256.ofNat x :: UInt256.ofNat m0 ::
             UInt256.ofNat (s32 input - 32) :: outerStack input
           memory := modulusMem s.memory input
           activeWords := loadWords s.activeWords input }

/-- State at the `R1B` guard entry `JUMPDEST` (pc 2901).  The guard dispatches
to `DOUBLE256` itself when the modulus's top bit is clear. -/
def setupExitState (s : State) (input : ByteArray) (m0 : Nat) : State :=
  { s with pc := UInt256.ofNat 2901
           stack := UInt256.ofNat 4096 :: UInt256.ofNat 1533 :: outerStack input
           memory := setupMem s.memory input m0
           activeWords := setupWords s.activeWords input }

set_option linter.unusedSimpArgs false in
theorem run_setupA (s : State) (input : ByteArray) (m0 : Nat)
    (hdata : s.executionEnv.calldata = input) (hrun : s.halt = .Running)
    (hsize : input.size < 2 ^ 256)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input)
    (hm0 : MachineState.readWord (modulusMem s.memory input) (s32 input - 32) =
      UInt256.ofNat m0) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupPathA (setupEntryState s input) =
      some (modLoadedState s input m0) := by
  simp only [modulusMem, varsMem, mstoreAt] at hm0
  have hn2 := limbs_ge_two input h32
  have hS := s32_le_1024 input hm
  have hSge : 32 ≤ s32 input := by unfold s32; omega
  have hsub32 : UInt256.ofNat (s32 input) - UInt256.ofNat 32 =
      UInt256.ofNat (s32 input - 32) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat hSge (by omega)
  have hsubms := sub_s32_msize input hm
  have hmodS := mod_word_self (s32_lt input hm)
  have hmodn := mod_word_self (limbs_lt input hm)
  have hmodb := mod_word_self (show 96 + baseSize input < 2 ^ 256 by omega)
  have hmodml := mod_word_self (show s32 input - 32 < 2 ^ 256 by omega)
  have hmodtl := mod_word_self (show 8224 + s32 input < 2 ^ 256 by omega)
  have hmodsz := mod_word_self hsize
  have hmodms := mod_word_self (show modulusSize input < 2 ^ 256 by omega)
  have hmodmoff := mod_word_self (modOffset_lt input hb he)
  have hmodsub := mod_word_self (show s32 input - modulusSize input < 2 ^ 256 by omega)
  simp (config := { maxSteps := 1000000 })
    [setupPathA, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     setupEntryState, modLoadedState, outerStack, modulusMem, varsMem, mstoreAt,
     loadWords, awNext, State.activeWordsAfterUInt256,
     hdata, hrun, push0_word, hsub32, hsubms, hm0,
     hmodS, hmodn, hmodb, hmodml, hmodtl, hmodsz, hmodms, hmodmoff, hmodsub,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_setupB (s : State) (input : ByteArray) (m0 : Nat)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupPathB (modLoadedState s input m0) =
      some (newtonState s input m0 (newton4 m0) 1481) := by
  simp (config := { maxSteps := 1000000 })
    [setupPathB, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     modLoadedState, newtonState, outerStack, newton4, hrun, newton_word_step,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_setupC (s : State) (input : ByteArray) (m0 : Nat)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupPathC
        (newtonState s input m0 (newton4 m0) 1481) =
      some (newtonState s input m0 (newton8 m0) 1509) := by
  simp (config := { maxSteps := 1000000 })
    [setupPathC, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     newtonState, outerStack, newton8, hrun, newton_word_step,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_setupD (s : State) (input : ByteArray) (m0 : Nat)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupPathD
        (newtonState s input m0 (newton8 m0) 1509) =
      some (setupExitState s input m0) := by
  have hmodminv : ∀ v : Nat,
      negWord v %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      negWord v := fun v => Nat.mod_eq_of_lt (negWord_lt v)
  simp (config := { maxSteps := 1000000 })
    [setupPathD, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     newtonState, setupExitState, outerStack, setupMem, mstoreAt, setupWords,
     awNext, State.activeWordsAfterUInt256, hcode, hrun, push0_word, neg_word,
     hmodminv, jumpDest2901,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]

/-! ## Reading the setup block's memory back -/

theorem byteFrom_eq (bs : ByteArray) (i : Nat) :
    YulSemantics.EVM.byteFrom bs.toList i = bs[i]?.getD 0 := by
  unfold YulSemantics.EVM.byteFrom
  rw [YulEvmCompiler.ByteArray.toList_eq_data, List.getD_eq_getElem?_getD,
    Array.getElem?_toList]
  rfl

set_option linter.unusedSimpArgs false in
theorem bytesToNatPadded_eq_zero (bs : ByteArray) (off : Nat) : ∀ n : Nat,
    (∀ i, i < n → bs[off + i]?.getD 0 = 0) →
    Precompile.bytesToNatPadded bs off n = 0
  | 0, _ => Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width bs off
  | n + 1, h => by
      have hb : YulSemantics.EVM.byteFrom bs.toList (off + n) = 0 := by
        rw [byteFrom_eq]
        exact h n (by omega)
      have hih := bytesToNatPadded_eq_zero bs off n (fun i hi => h i (by omega))
      simp [Challenge.EvmProof.Bytes.bytesToNatPadded_succ, hih, hb]

theorem readWord_empty (target : Nat) :
    MachineState.readWord ByteArray.empty target = UInt256.ofNat 0 := by
  unfold MachineState.readWord
  congr 1
  exact bytesToNatPadded_eq_zero ByteArray.empty target 32
    (fun i _ => Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le _ _ (by simp))

/-- Every byte of a zero-padded read that starts at or past the end is zero. -/
theorem readPadded_beyond_getElem (bs : ByteArray) (start n i : Nat)
    (hstart : bs.size ≤ start) :
    (MachineState.readPadded bs start n)[i]?.getD 0 = 0 := by
  rw [Challenge.EvmProof.Memory.readPadded_getElem?_getD]
  split
  · exact Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le bs (start + i)
      (by omega)
  · rfl

theorem readWord_mstoreAt_ne (mem : ByteArray) (addr value target : Nat)
    (h : target + 32 ≤ addr ∨ addr + 32 ≤ target) :
    MachineState.readWord (mstoreAt mem addr value) target =
      MachineState.readWord mem target := by
  unfold mstoreAt
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  exact h

theorem readWord_mstoreAt_self (mem : ByteArray) (addr value : Nat)
    (hv : value < 2 ^ 256) :
    MachineState.readWord (mstoreAt mem addr value) addr = UInt256.ofNat value := by
  unfold mstoreAt
  exact Challenge.EvmProof.Memory.readWord_writeBytes_of_lt mem addr value
    (by rw [pow_256_32]; exact hv)

theorem readWord_writeBytes_ne (mem src : ByteArray) (start target : Nat)
    (h : target + 32 ≤ start ∨ start + src.size ≤ target) :
    MachineState.readWord (MachineState.writeBytes mem src start) target =
      MachineState.readWord mem target :=
  Challenge.EvmProof.Memory.readWord_writeBytes_disjoint mem src target start h

/-- Reads in the variable area see straight through the modulus copies and the
two trailing stores. -/
theorem readWord_setupMem_var (mem : ByteArray) (input : ByteArray) (m0 target : Nat)
    (hm : modulusSize input ≤ 1024) (hlo : 9344 ≤ target)
    (hne : target + 32 ≤ 9376 ∨ 9376 + 32 ≤ target) :
    MachineState.readWord (setupMem mem input m0) target =
      MachineState.readWord (varsMem mem input) target := by
  have hS := s32_le_1024 input hm
  have hms := modulusSize_le_s32 input
  unfold setupMem modulusMem
  rw [readWord_mstoreAt_ne _ _ _ _ (Or.inr (by omega)),
    readWord_mstoreAt_ne _ _ _ _ hne,
    readWord_writeBytes_ne _ _ _ _ (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    readWord_writeBytes_ne _ _ _ _ (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega))]

theorem readWord_V_S32 (mem : ByteArray) (input : ByteArray) (m0 : Nat)
    (hm : modulusSize input ≤ 1024) :
    MachineState.readWord (setupMem mem input m0) 9344 =
      UInt256.ofNat (s32 input) := by
  rw [readWord_setupMem_var mem input m0 9344 hm (by omega) (Or.inl (by omega))]
  unfold varsMem
  rw [readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    readWord_mstoreAt_self _ _ _ (s32_lt input hm)]

theorem readWord_V_N (mem : ByteArray) (input : ByteArray) (m0 : Nat)
    (hm : modulusSize input ≤ 1024) :
    MachineState.readWord (setupMem mem input m0) 9504 =
      UInt256.ofNat (limbs input) := by
  rw [readWord_setupMem_var mem input m0 9504 hm (by omega) (Or.inr (by omega))]
  unfold varsMem
  rw [readWord_mstoreAt_ne _ _ _ _ (Or.inr (by omega)),
    readWord_mstoreAt_ne _ _ _ _ (Or.inr (by omega)),
    readWord_mstoreAt_ne _ _ _ _ (Or.inr (by omega)),
    readWord_mstoreAt_self _ _ _ (limbs_lt input hm)]

theorem readWord_V_EOFF (mem : ByteArray) (input : ByteArray) (m0 : Nat)
    (hm : modulusSize input ≤ 1024) (hb : baseSize input ≤ 1024) :
    MachineState.readWord (setupMem mem input m0) 9472 =
      UInt256.ofNat (96 + baseSize input) := by
  rw [readWord_setupMem_var mem input m0 9472 hm (by omega) (Or.inr (by omega))]
  unfold varsMem
  rw [readWord_mstoreAt_ne _ _ _ _ (Or.inr (by omega)),
    readWord_mstoreAt_ne _ _ _ _ (Or.inr (by omega)),
    readWord_mstoreAt_self _ _ _ (by omega)]

theorem readWord_V_ML (mem : ByteArray) (input : ByteArray) (m0 : Nat)
    (hm : modulusSize input ≤ 1024) :
    MachineState.readWord (setupMem mem input m0) 9408 =
      UInt256.ofNat (s32 input - 32) := by
  have hS := s32_le_1024 input hm
  rw [readWord_setupMem_var mem input m0 9408 hm (by omega) (Or.inr (by omega))]
  unfold varsMem
  rw [readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    readWord_mstoreAt_self _ _ _ (by omega)]

theorem readWord_V_TL (mem : ByteArray) (input : ByteArray) (m0 : Nat)
    (hm : modulusSize input ≤ 1024) :
    MachineState.readWord (setupMem mem input m0) 9440 =
      UInt256.ofNat (8224 + s32 input) := by
  have hS := s32_le_1024 input hm
  rw [readWord_setupMem_var mem input m0 9440 hm (by omega) (Or.inr (by omega))]
  unfold varsMem
  rw [readWord_mstoreAt_self _ _ _ (by omega)]

theorem readWord_V_MINV (mem : ByteArray) (input : ByteArray) (m0 : Nat) :
    MachineState.readWord (setupMem mem input m0) 9376 =
      UInt256.ofNat (negWord (newton8 m0)) := by
  unfold setupMem
  rw [readWord_mstoreAt_ne _ _ _ _ (Or.inr (by omega)),
    readWord_mstoreAt_self _ _ _ (negWord_lt _)]

/-! ## The modulus block -/

/-- The `n`-limb block at `ptr` always represents the big-endian number formed
by its `32 n` bytes. -/
theorem fastRepresents_bytes (bs : ByteArray) (ptr count : Nat) :
    Model.FastRepresents bs ptr count
      (Precompile.bytesToNatPadded bs ptr (32 * count)) := by
  apply Model.fastRepresents_of_limbs
  · rw [Limbs.pow_radix]
    exact Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow _ _ _
  · intro k hk
    rw [Challenge.EvmProof.Bytes.readWord_toNat]
    have hrk : Limbs.radix ^ k = 256 ^ (32 * k) := Limbs.pow_radix k
    have hpos : 0 < Limbs.radix ^ k := Nat.pow_pos Limbs.radix_pos
    have hBlt : Precompile.bytesToNatPadded bs (ptr + 32 * (count - 1 - k)) 32
        < Limbs.radix := by
      rw [Limbs.radix_eq]
      exact Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow _ _ _
    have hClt : Precompile.bytesToNatPadded bs
        (ptr + 32 * (count - 1 - k) + 32) (32 * k) < Limbs.radix ^ k := by
      rw [hrk]
      exact Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow _ _ _
    have hA := Challenge.EvmProof.Bytes.bytesToNatPadded_add bs ptr
      (32 * (count - 1 - k)) (32 + 32 * k)
    rw [show 32 * (count - 1 - k) + (32 + 32 * k) = 32 * count from by omega] at hA
    have hB := Challenge.EvmProof.Bytes.bytesToNatPadded_add bs
      (ptr + 32 * (count - 1 - k)) 32 (32 * k)
    have hpow : (256 : Nat) ^ (32 + 32 * k) = Limbs.radix ^ k * Limbs.radix := by
      rw [hrk, Limbs.radix_eq, ← pow_add]
      congr 1
      omega
    have hring : ∀ a b c : Nat,
        a * (Limbs.radix ^ k * Limbs.radix) + (b * Limbs.radix ^ k + c)
          = Limbs.radix ^ k * (a * Limbs.radix + b) + c := by
      intro a b c
      ring
    rw [hA, hB, hpow, ← hrk, hring, Nat.mul_add_div hpos,
      Nat.div_eq_of_lt hClt, Nat.add_zero, Nat.mul_add_mod',
      Nat.mod_eq_of_lt hBlt]

theorem modulusMem_zero_region (mem : ByteArray) (input : ByteArray) (i : Nat)
    (hi : i < s32 input - modulusSize input) :
    (modulusMem mem input)[0 + i]?.getD 0 = 0 := by
  have hms := modulusSize_le_s32 input
  unfold modulusMem
  rw [MachineState.writeBytes_getElem?_getD,
    if_neg (by simp only [Challenge.EvmProof.Memory.readPadded_size]; omega),
    MachineState.writeBytes_getElem?_getD,
    if_pos (by simp only [Challenge.EvmProof.Memory.readPadded_size]; omega)]
  exact readPadded_beyond_getElem input input.size (s32 input) _ le_rfl

theorem modulusMem_value (mem : ByteArray) (input : ByteArray) :
    Precompile.bytesToNatPadded (modulusMem mem input) 0 (s32 input) =
      modulus input := by
  have hms := modulusSize_le_s32 input
  have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add (modulusMem mem input) 0
    (s32 input - modulusSize input) (modulusSize input)
  rw [show s32 input - modulusSize input + modulusSize input = s32 input from by omega]
    at hsplit
  have hhigh : Precompile.bytesToNatPadded (modulusMem mem input) 0
      (s32 input - modulusSize input) = 0 :=
    bytesToNatPadded_eq_zero _ _ _ (fun i hi => modulusMem_zero_region mem input i hi)
  have hsize : (MachineState.readPadded input (modOffset input)
      (modulusSize input)).size = modulusSize input :=
    Challenge.EvmProof.Memory.readPadded_size _ _ _
  have hsame := Challenge.EvmProof.Memory.readPadded_writeBytes_same
    (MachineState.writeBytes (varsMem mem input)
      (MachineState.readPadded input input.size (s32 input)) 0)
    (MachineState.readPadded input (modOffset input) (modulusSize input))
    (s32 input - modulusSize input)
  rw [hsize] at hsame
  have hlow : Precompile.bytesToNatPadded (modulusMem mem input)
      (0 + (s32 input - modulusSize input)) (modulusSize input) = modulus input := by
    rw [Nat.zero_add]
    unfold modulusMem modulus Precompile.bytesToNatPadded
    rw [hsame]
  rw [hsplit, hhigh, hlow, Nat.zero_mul, Nat.zero_add]

theorem modulusMem_represents (mem : ByteArray) (input : ByteArray) :
    Model.FastRepresents (modulusMem mem input) 0 (limbs input) (modulus input) := by
  have h := fastRepresents_bytes (modulusMem mem input) 0 (limbs input)
  rw [show 32 * limbs input = s32 input from rfl, modulusMem_value mem input] at h
  exact h

/-- The modulus block at `0x0000` holds `m` in `n` limbs. -/
theorem setupMem_represents (mem : ByteArray) (input : ByteArray) (m0 : Nat)
    (hm : modulusSize input ≤ 1024) :
    Model.FastRepresents (setupMem mem input m0) 0 (limbs input) (modulus input) := by
  have hS := s32_le_1024 input hm
  have h32n : 32 * limbs input = s32 input := rfl
  unfold setupMem mstoreAt
  exact Model.fastRepresents_writeWord_disjoint _ 4096 0 _ _ 1 (Or.inr (by omega))
    (Model.fastRepresents_writeWord_disjoint _ 9376 0 _ _ _ (Or.inr (by omega))
      (modulusMem_represents mem input))

/-- The least significant limb of the modulus, as the block holds it. -/
theorem lowLimb_eq (mem : ByteArray) (input : ByteArray) (h32 : 32 < modulusSize input) :
    (MachineState.readWord (modulusMem mem input) (s32 input - 32)).toNat =
      modulus input % Limbs.radix := by
  have hn2 := limbs_ge_two input h32
  have h := Model.readWord_of_fastRepresents (modulusMem_represents mem input)
    (j := limbs input - 1) (by omega)
  rw [show (0 : Nat) + 32 * (limbs input - 1) = s32 input - 32 from by
    unfold s32; omega] at h
  rw [h, show limbs input - 1 - (limbs input - 1) = 0 from by omega, pow_zero,
    Nat.div_one]

/-! ## The `R1` block and `minv` -/

/-- Nothing in the setup block touches memory between `0x1020` and `0x2480`. -/
theorem readWord_setupMem_high (input : ByteArray) (m0 target : Nat)
    (hm : modulusSize input ≤ 1024) (hlo : 4128 ≤ target) (hhi : target + 32 ≤ 9344) :
    MachineState.readWord (setupMem ByteArray.empty input m0) target =
      UInt256.ofNat 0 := by
  have hS := s32_le_1024 input hm
  have hms := modulusSize_le_s32 input
  unfold setupMem modulusMem varsMem
  rw [readWord_mstoreAt_ne _ _ _ _ (Or.inr (by omega)),
    readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    readWord_writeBytes_ne _ _ _ _
      (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    readWord_writeBytes_ne _ _ _ _
      (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    readWord_empty]

/-- The `R1` block at `0x1000` holds `radix ^ (n - 1)`. -/
theorem setupMem_R1 (input : ByteArray) (m0 : Nat)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input) :
    Model.FastRepresents (setupMem ByteArray.empty input m0) 4096 (limbs input)
      (Limbs.radix ^ (limbs input - 1)) := by
  have hn2 := limbs_ge_two input h32
  have hn32 := limbs_le_32 input hm
  have hS := s32_le_1024 input hm
  have hrpos : 0 < Limbs.radix := Limbs.radix_pos
  apply Model.fastRepresents_of_limbs
  · exact Nat.pow_lt_pow_right Limbs.radix_gt_one (by omega)
  · intro k hk
    by_cases hkt : k = limbs input - 1
    · subst hkt
      rw [show limbs input - 1 - (limbs input - 1) = 0 from by omega, Nat.mul_zero,
        Nat.add_zero]
      unfold setupMem
      rw [readWord_mstoreAt_self _ _ _ (by norm_num),
        toNat_ofNat_self (show (1 : Nat) < 2 ^ 256 by norm_num),
        Nat.div_self (Nat.pow_pos hrpos),
        Nat.mod_eq_of_lt Limbs.radix_gt_one]
    · have hjpos : 1 ≤ limbs input - 1 - k := by omega
      have hz : Limbs.radix ^ (limbs input - 1 - k) % Limbs.radix = 0 := by
        obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hjpos
        rw [hj, pow_add, pow_one, Nat.mul_mod_right]
      rw [readWord_setupMem_high input m0 _ hm (by omega) (by omega),
        toNat_ofNat_self (show (0 : Nat) < 2 ^ 256 by norm_num),
        Nat.pow_div (show k ≤ limbs input - 1 by omega) hrpos, hz]

/-- `minv` satisfies the CIOS precondition `m[0] · minv ≡ -1 (mod 2^256)`. -/
theorem minv_correct (input : ByteArray) (m0 : Nat)
    (hodd : modulus input % 2 = 1) (hm0 : m0 = modulus input % Limbs.radix) :
    (m0 * negWord (newton8 m0) + 1) % Limbs.radix = 0 := by
  have hodd0 : m0 % 2 = 1 := by rw [hm0]; exact Model.low_limb_odd hodd
  have height : m0 * Model.newtonIter m0 8 % Limbs.radix = 1 :=
    Model.newtonIter_eight hodd0
  have hlt : Model.newtonIter m0 8 < Limbs.radix := by
    rw [show (8 : Nat) = 7 + 1 from rfl, Model.newtonIter_succ]
    exact Model.newtonStep_lt _ _
  have hpos : 0 < Model.newtonIter m0 8 := by
    rcases Nat.eq_zero_or_pos (Model.newtonIter m0 8) with hz | hp
    · rw [hz, Nat.mul_zero, Nat.zero_mod] at height
      omega
    · exact hp
  have hm0lt : m0 < Limbs.radix := by
    rw [hm0]
    exact Nat.mod_lt _ Limbs.radix_pos
  have hneg : negWord (newton8 m0) = Limbs.radix - Model.newtonIter m0 8 := by
    unfold negWord
    rw [newton8_eq, Nat.mod_eq_of_lt hlt]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hneg]
  refine Model.minv_spec ?_ (le_of_lt hlt)
  rw [Nat.mod_eq_of_lt hm0lt]
  exact height

/-! ## The success trace and its postconditions -/

def gasSteps_setup (s : State) (input : ByteArray) (m0 : Nat)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hsize : input.size < 2 ^ 256)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input)
    (hm0 : MachineState.readWord (modulusMem s.memory input) (s32 input - 32) =
      UInt256.ofNat m0) :
    Challenge.EvmProof.GasSteps (setupEntryState s input) (setupExitState s input m0) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka setupPathA
        (s := setupEntryState s input) hcode hfork
        (run_setupA s input m0 hdata hrun hsize hb he hm h32 hm0) hrun hnp).trans
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka setupPathB
          (s := modLoadedState s input m0) hcode hfork
          (run_setupB s input m0 hrun) hrun hnp).trans
      ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
          Artifact.submissionArtifact .Osaka setupPathC
            (s := newtonState s input m0 (newton4 m0) 1481) hcode hfork
            (run_setupC s input m0 hrun) hrun hnp).trans
        (Challenge.EvmProof.Stepper.runLocatedBlock_sound
          Artifact.submissionArtifact .Osaka setupPathD
            (s := newtonState s input m0 (newton8 m0) 1509) hcode hfork
            (run_setupD s input m0 hcode hrun) hrun hnp)))

def gasSteps_fastPath_of (s : State) (input : ByteArray) (m0 : Nat)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hsize : input.size < 2 ^ 256)
    (hm0 : MachineState.readWord (modulusMem s.memory input) (s32 input - 32) =
      UInt256.ofNat m0)
    (hpath : FastPath input) :
    Challenge.EvmProof.GasSteps (entryState s) (setupExitState s input m0) :=
  (gasSteps_entry_pass s input hdata hcode hfork hrun hnp hpath.1).trans
    ((gasSteps_sizeCheck_pass s input hdata hcode hfork hrun hnp
        hpath.2.1.1 hpath.2.1.2.1 hpath.2.1.2.2).trans
      ((gasSteps_topCheck_pass s input hdata hcode hfork hrun hnp
          hpath.2.1.1 hpath.2.1.2.1 hpath.2.1.2.2 hpath.1
          ((topLimb_ne_zero_iff input hpath.1).mpr hpath.2.2.1)).trans
        ((gasSteps_oddCheck_pass s input hdata hcode hfork hrun hnp
            hpath.2.1.1 hpath.2.1.2.1 hpath.2.1.2.2 hpath.1 hpath.2.2.2).trans
          (gasSteps_setup s input m0 hdata hcode hfork hrun hnp hsize
            hpath.2.1.1 hpath.2.1.2.1 hpath.2.1.2.2 hpath.1 hm0))))

/-- The least significant limb of the modulus as the loaded block holds it. -/
def lowLimb (input : ByteArray) : Nat :=
  (MachineState.readWord (modulusMem ByteArray.empty input) (s32 input - 32)).toNat

/-- `minv = -m[0]⁻¹ mod 2^256`, as the block stores it at `V_MINV`. -/
def minvValue (input : ByteArray) : Nat := negWord (newton8 (lowLimb input))

/-- The state the setup reaches: the `DOUBLE256` entry `JUMPDEST` at pc 1911. -/
def fastSetupState (input : ByteArray) : State :=
  setupExitState (initialState submissionBytecode input 0) input (lowLimb input)

/-- Memory at the end of the setup block, for the real initial state. -/
def fastSetupMemory (input : ByteArray) : ByteArray :=
  setupMem ByteArray.empty input (lowLimb input)

theorem fastSetupState_memory (input : ByteArray) :
    (fastSetupState input).memory = fastSetupMemory input := rfl

theorem fastSetupState_pc (input : ByteArray) :
    (fastSetupState input).pc = UInt256.ofNat 2901 := rfl

theorem fastSetupState_stack (input : ByteArray) :
    (fastSetupState input).stack =
      UInt256.ofNat 4096 :: UInt256.ofNat 1533 :: outerStack input := rfl

/-- **Setup certificate.**  For every calldata satisfying the fast-path
precondition (and the `ValidInput` bound on the calldata length), execution
runs from the state the retargeted entry produces to the `R1B` guard, with the modulus loaded, `minv` computed and `R1` initialised. -/
def gasSteps_fastSetup (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hpath : FastPath input) :
    Challenge.EvmProof.GasSteps (Main.trampolineState input 1314)
      (fastSetupState input) :=
  Challenge.EvmProof.GasSteps.cast
    (gasSteps_fastPath_of (initialState submissionBytecode input 0) input
      (lowLimb input) rfl rfl rfl rfl deployAddress_not_precompile hsize
      (Challenge.EvmProof.Word.word_eq_ofNat_toNat _) hpath)
    (entryState_initial input) rfl

/-! ## Postconditions of the setup block -/

theorem fastSetup_modulus (input : ByteArray) (hpath : FastPath input) :
    Model.FastRepresents (fastSetupMemory input) 0 (limbs input) (modulus input) :=
  setupMem_represents ByteArray.empty input (lowLimb input) hpath.2.1.2.2

theorem fastSetup_R1 (input : ByteArray) (hpath : FastPath input) :
    Model.FastRepresents (fastSetupMemory input) 4096 (limbs input)
      (Limbs.radix ^ (limbs input - 1)) :=
  setupMem_R1 input (lowLimb input) hpath.2.1.2.2 hpath.1

theorem fastSetup_V_S32 (input : ByteArray) (hpath : FastPath input) :
    MachineState.readWord (fastSetupMemory input) 9344 = UInt256.ofNat (s32 input) :=
  readWord_V_S32 ByteArray.empty input (lowLimb input) hpath.2.1.2.2

theorem fastSetup_V_N (input : ByteArray) (hpath : FastPath input) :
    MachineState.readWord (fastSetupMemory input) 9504 = UInt256.ofNat (limbs input) :=
  readWord_V_N ByteArray.empty input (lowLimb input) hpath.2.1.2.2

theorem fastSetup_V_ML (input : ByteArray) (hpath : FastPath input) :
    MachineState.readWord (fastSetupMemory input) 9408 =
      UInt256.ofNat (s32 input - 32) :=
  readWord_V_ML ByteArray.empty input (lowLimb input) hpath.2.1.2.2

theorem fastSetup_V_TL (input : ByteArray) (hpath : FastPath input) :
    MachineState.readWord (fastSetupMemory input) 9440 =
      UInt256.ofNat (8224 + s32 input) :=
  readWord_V_TL ByteArray.empty input (lowLimb input) hpath.2.1.2.2

theorem fastSetup_V_EOFF (input : ByteArray) (hpath : FastPath input) :
    MachineState.readWord (fastSetupMemory input) 9472 =
      UInt256.ofNat (96 + baseSize input) :=
  readWord_V_EOFF ByteArray.empty input (lowLimb input) hpath.2.1.2.2 hpath.2.1.1

theorem fastSetup_V_MINV (input : ByteArray) :
    MachineState.readWord (fastSetupMemory input) 9376 =
      UInt256.ofNat (minvValue input) :=
  readWord_V_MINV ByteArray.empty input (lowLimb input)

theorem fastSetup_lowLimb (input : ByteArray) (hpath : FastPath input) :
    lowLimb input = modulus input % Limbs.radix :=
  lowLimb_eq ByteArray.empty input hpath.1

/-- `m[0] · minv ≡ -1 (mod 2^256)`. -/
theorem fastSetup_minv (input : ByteArray) (hpath : FastPath input) :
    (lowLimb input * minvValue input + 1) % Limbs.radix = 0 :=
  minv_correct input (lowLimb input) hpath.2.2.2 (fastSetup_lowLimb input hpath)

/-! ## Arithmetic consequences later modules need -/

theorem fastSetup_limbs_ge_two (input : ByteArray) (hpath : FastPath input) :
    2 ≤ limbs input := limbs_ge_two input hpath.1

theorem fastSetup_limbs_le_32 (input : ByteArray) (hpath : FastPath input) :
    limbs input ≤ 32 := limbs_le_32 input hpath.2.1.2.2

theorem fastSetup_s32_eq (input : ByteArray) : s32 input = 32 * limbs input := rfl

theorem fastSetup_modulus_odd (input : ByteArray) (hpath : FastPath input) :
    modulus input % 2 = 1 := hpath.2.2.2

theorem fastSetup_modulus_bounds (input : ByteArray) (hpath : FastPath input) :
    Limbs.radix ^ (limbs input - 1) ≤ modulus input ∧
      modulus input < Limbs.radix ^ limbs input :=
  ⟨hpath.2.2.1, modulus_lt input⟩

/-- The value held in the modulus block is exactly the EIP-198 modulus operand
read out of the calldata. -/
theorem fastSetup_modulus_eq (input : ByteArray) :
    modulus input =
      Precompile.bytesToNatPadded input (96 + baseSize input + exponentSize input)
        (modulusSize input) := rfl

/-! ## The memory high-water mark the later subroutines assume

Every address the fast path touches lies below `0x2500`; the setup block's
`MSTORE V_N` at `0x2520` makes 298 words active, and nothing afterwards
extends the mark.  `Fast.Csub`, `Fast.Double` and `Fast.Monpro` take
`296 ≤ s.activeWords.toNat` as a hypothesis and rely on this. -/

theorem activeWordsAfter_eq (curr off sz : Nat) (hsz : sz ≠ 0) :
    MachineState.activeWordsAfter curr off sz = max curr ((off + sz - 1) / 32 + 1) := by
  unfold MachineState.activeWordsAfter
  rw [if_neg hsz]

theorem setupWords_initial (input : ByteArray) (hm : modulusSize input ≤ 1024)
    (h32 : 32 < modulusSize input) :
    setupWords (UInt256.ofNat 0) input = UInt256.ofNat 298 := by
  have hn2 := limbs_ge_two input h32
  have hS := s32_le_1024 input hm
  have hSge : 32 ≤ s32 input := by unfold s32; omega
  have hms := modulusSize_le_s32 input
  have hSne : s32 input ≠ 0 := by omega
  have hmsne : modulusSize input ≠ 0 := by omega
  simp only [setupWords, loadWords, awNext,
    activeWordsAfter_eq _ _ 32 (by norm_num),
    activeWordsAfter_eq _ _ (s32 input) hSne,
    activeWordsAfter_eq _ _ (modulusSize input) hmsne,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  congr 1
  omega

/-- After the setup block exactly 298 words are active. -/
theorem fastSetup_activeWords (input : ByteArray) (hpath : FastPath input) :
    (fastSetupState input).activeWords = UInt256.ofNat 298 :=
  setupWords_initial input hpath.2.1.2.2 hpath.1

/-- The high-water bound the three subroutine modules assume. -/
theorem fastSetup_activeWords_ge (input : ByteArray) (hpath : FastPath input) :
    296 ≤ (fastSetupState input).activeWords.toNat := by
  rw [fastSetup_activeWords input hpath,
    toNat_ofNat_self (show (298 : Nat) < 2 ^ 256 by norm_num)]
  omega

/-- The fast-path precondition is decided, as `Fast.Correct`'s `decide` field
requires. -/
theorem fastPath_em (input : ByteArray) : FastPath input ∨ ¬ FastPath input :=
  Classical.em _


end Challenge.Modexp.Submission.Proofs.Fast.Setup
