import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P16
import Challenge.Modexp.Submission.Proofs.Fast.Setup
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# The `LZ` head of the exponent-byte loop

`LZ` occupies instruction indices 1781..1815 (pc 2922..2970).  It is entered
at pc 2922 with the byte index `i` on top of the driver frame, loads exponent
byte `i` exactly as the code it replaces did, and then chooses the mask the
inner bit loop starts from:

* for `i ≠ 0` it is `0x80`, as before;
* for `i = 0` it is the highest set bit of the byte, so the bit loop starts at
  the exponent's leading one instead of at bit 7.

Both arms rejoin the bit loop at pc 1789.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Lz

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

attribute [local simp] List.getElem?_cons_zero

/-! ## Memory-expansion bookkeeping

`Fast.Exp` carries the same two lemmas, but it imports this module, so they are
restated here for the `V_EOFF` load. -/

theorem activeWordsAfter_fix (curr off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 9536) (hcurr : 298 ≤ curr) :
    MachineState.activeWordsAfter curr off sz = curr := by
  unfold MachineState.activeWordsAfter
  simp only [hsz, if_false]
  exact Nat.max_eq_left (by omega)

theorem activeWords_fix (s : State) (off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 9536) (hact : 298 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat off sz) =
      s.activeWords := by
  rw [activeWordsAfter_fix _ off sz hsz hoff hact]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm

/-! ## The mask -/

/-- The three smear steps, in the operand order the `OR`s produce them:
`OR` pops the shifted copy first. -/
def sm1 (w : Nat) : Nat := (w >>> 1) ||| w
def sm2 (w : Nat) : Nat := (sm1 w >>> 2) ||| sm1 w
def sm3 (w : Nat) : Nat := (sm2 w >>> 4) ||| sm2 w

/-- The smear halved and incremented: the highest set bit of a byte, and `1`
for a zero byte. -/
def topBit (w : Nat) : Nat := (sm3 w >>> 1) + 1

/-- Its exponent. -/
def topExp (w : Nat) : Nat :=
  if 128 ≤ w then 7 else if 64 ≤ w then 6 else if 32 ≤ w then 5 else
  if 16 ≤ w then 4 else if 8 ≤ w then 3 else if 4 ≤ w then 2 else
  if 2 ≤ w then 1 else 0

/-- **The mask is a power of two that dominates the byte.**  Everything the
skipped iterations of the bit loop would have tested is zero. -/
theorem topBit_spec (w : Nat) (hw : w < 256) :
    topBit w = 2 ^ topExp w ∧ topExp w ≤ 7 ∧ w < 2 ^ (topExp w + 1) := by
  interval_cases w <;> exact ⟨by decide, by decide, by decide⟩

/-! ## States at the block boundaries -/

/-- The `LZ` entry, pc 2922.  The driver frame below the byte index is left
abstract so that this module does not depend on `Fast.Exp`. -/
def lzEntry (s : State) (mem : ByteArray) (i : Nat) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2922
           stack := UInt256.ofNat i :: rest
           memory := mem }

/-- pc 2938, the arm every byte after the first takes. -/
def lzOther (s : State) (mem : ByteArray) (i w : Nat) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2938
           stack := UInt256.ofNat w :: UInt256.ofNat i :: rest
           memory := mem }

/-- pc 2944, the arm byte `0` takes. -/
def lzFirst (s : State) (mem : ByteArray) (i w : Nat) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2944
           stack := UInt256.ofNat w :: UInt256.ofNat i :: rest
           memory := mem }

/-- The bit-loop head both arms rejoin, pc 1789. -/
def lzJoin (s : State) (mem : ByteArray) (i w mask : Nat)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1789
           stack := UInt256.ofNat mask :: UInt256.ofNat w :: UInt256.ofNat i :: rest
           memory := mem }

/-! ## Traces

The byte the block loads is left abstract, as `hbyte`, so that this module
does not need `Fast.Exp`'s `expByte`. -/

/-- Instructions 1781..1792 with `i = 0`: load the byte, take the first-byte arm. -/
theorem run_lzHead_first (s : State) (mem input : ByteArray) (bsize i w : Nat)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hdata : s.executionEnv.calldata = input)
    (hb : bsize ≤ 1024) (hi : i ≤ 1024) (hact : 298 ≤ s.activeWords.toNat)
    (heoff : MachineState.readWord mem 9472 = UInt256.ofNat (96 + bsize))
    (hbyte : UInt256.byteAt ⟨0⟩ (MachineState.readWord input (96 + bsize + i)) =
      UInt256.ofNat w)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) (hzero : i = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1781
      (lzEntry s mem i rest) = some (lzFirst s mem i w rest) := by
  subst hzero
  have hmod : (96 + bsize + 0) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 96 + bsize + 0 :=
    Setup.mod_word_self (Nat.lt_of_le_of_lt (show 96 + bsize + 0 ≤ 2144 by omega)
      (by norm_num))
  have hfix : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      9472 32) = s.activeWords :=
    activeWords_fix s 9472 32 (by omega) (by omega) hact
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have htrue : UInt256.isTrue (UInt256.ofNat 1) := by decide
  have hiz : UInt256.isZero (UInt256.ofNat 0) = UInt256.ofNat 1 := by decide
  simp only [Nat.add_zero] at hmod hbyte
  simp (config := { maxSteps := 600000 }) [blk1781, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lzEntry, lzFirst, hdata, hrun, hcode, heoff, hmod, hfix, hbyte, hiz, htrue,
    hc1, hc2, hc3, hc4, jumpDest2944, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

/-- Instructions 1781..1792 with `i ≠ 0`: load the byte, fall through. -/
theorem run_lzHead_other (s : State) (mem input : ByteArray) (bsize i w : Nat)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hdata : s.executionEnv.calldata = input)
    (hb : bsize ≤ 1024) (hi : i ≤ 1024) (hact : 298 ≤ s.activeWords.toNat)
    (heoff : MachineState.readWord mem 9472 = UInt256.ofNat (96 + bsize))
    (hbyte : UInt256.byteAt ⟨0⟩ (MachineState.readWord input (96 + bsize + i)) =
      UInt256.ofNat w)
    (_hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) (hne : i ≠ 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1781
      (lzEntry s mem i rest) = some (lzOther s mem i w rest) := by
  have hmod : (96 + bsize + i) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 96 + bsize + i :=
    Setup.mod_word_self (Nat.lt_of_le_of_lt (show 96 + bsize + i ≤ 2144 by omega)
      (by norm_num))
  have hfix : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      9472 32) = s.activeWords :=
    activeWords_fix s 9472 32 (by omega) (by omega) hact
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hiz : UInt256.isZero (UInt256.ofNat i) = UInt256.ofNat 0 := by
    have hti : (UInt256.ofNat i).toNat = i := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hi (by norm_num))
    simp only [UInt256.isZero, hti, if_neg hne]
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  simp (config := { maxSteps := 600000 }) [blk1781, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lzEntry, lzOther, hdata, hrun, heoff, hmod, hfix, hbyte, hiz, hfalse,
    hc1, hc2, hc3, hc4, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

/-! ## Word arithmetic for the smear

`Fast.Exp` carries `shr_ofNat` and a `land` companion, but it imports this
module. -/

theorem shr_ofNat' (v k : Nat) (hv : v < 2 ^ 256) (hk : k < 256) :
    UInt256.shiftRight (UInt256.ofNat v) (UInt256.ofNat k) =
      UInt256.ofNat (v >>> k) := by
  rw [Challenge.EvmProof.Word.shiftRight_ofNat hv hk]

theorem lor_ofNat (a b : Nat) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    UInt256.lor (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a ||| b) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_lor,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt (Nat.or_lt_two_pow ha hb)]

theorem sm_lt (w : Nat) (hw : w < 256) :
    sm1 w < 256 ∧ sm2 w < 256 ∧ sm3 w < 256 := by
  interval_cases w <;> exact ⟨by decide, by decide, by decide⟩

/-! ## The two rejoining arms -/

/-- Instructions 1793..1795: every byte after the first starts the bit loop at
`0x80`, exactly as the code this replaces did. -/
theorem run_lzOther (s : State) (mem : ByteArray) (i w : Nat)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1793
      (lzOther s mem i w rest) = some (lzJoin s mem i w 128 rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  simp (config := { maxSteps := 400000 }) [blk1793, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lzOther, lzJoin, hrun, hcode, hc2, hc3, hc4, jumpDest1789,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

/-- Instructions 1796..1815: byte `0` starts the bit loop at its highest set
bit, so the exponent's leading zeros are never squared over. -/
theorem run_lzFirst (s : State) (mem : ByteArray) (i w : Nat)
    (rest : List UInt256) (hcap : rest.length ≤ 1008) (hw : w < 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1796
      (lzFirst s mem i w rest) = some (lzJoin s mem i w (topBit w) rest) := by
  obtain ⟨h1, h2, h3⟩ := sm_lt w hw
  have b0 : w < 2 ^ 256 := by omega
  have b1 : sm1 w < 2 ^ 256 := by omega
  have b2 : sm2 w < 2 ^ 256 := by omega
  have b3 : sm3 w < 2 ^ 256 := by omega
  have e1 : UInt256.shiftRight (UInt256.ofNat w) (UInt256.ofNat 1) =
      UInt256.ofNat (w >>> 1) := shr_ofNat' w 1 b0 (by norm_num)
  have e2 : UInt256.lor (UInt256.ofNat (w >>> 1)) (UInt256.ofNat w) =
      UInt256.ofNat (sm1 w) :=
    lor_ofNat _ _ (by omega) b0
  have e3 : UInt256.shiftRight (UInt256.ofNat (sm1 w)) (UInt256.ofNat 2) =
      UInt256.ofNat (sm1 w >>> 2) := shr_ofNat' _ 2 b1 (by norm_num)
  have e4 : UInt256.lor (UInt256.ofNat (sm1 w >>> 2)) (UInt256.ofNat (sm1 w)) =
      UInt256.ofNat (sm2 w) :=
    lor_ofNat _ _ (by omega) b1
  have e5 : UInt256.shiftRight (UInt256.ofNat (sm2 w)) (UInt256.ofNat 4) =
      UInt256.ofNat (sm2 w >>> 4) := shr_ofNat' _ 4 b2 (by norm_num)
  have e6 : UInt256.lor (UInt256.ofNat (sm2 w >>> 4)) (UInt256.ofNat (sm2 w)) =
      UInt256.ofNat (sm3 w) :=
    lor_ofNat _ _ (by omega) b2
  have e7 : UInt256.shiftRight (UInt256.ofNat (sm3 w)) (UInt256.ofNat 1) =
      UInt256.ofNat (sm3 w >>> 1) := shr_ofNat' _ 1 b3 (by norm_num)
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hcomm : (1 : Nat) + (sm3 w >>> 1) = topBit w := by
    simp only [topBit]; omega
  simp (config := { maxSteps := 600000 }) [blk1796, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lzFirst, lzJoin, hrun, hcode, hc2, hc3, hc4, hc5, hcomm, jumpDest1789,
    e1, e2, e3, e4, e5, e6, e7,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Fast.Lz
