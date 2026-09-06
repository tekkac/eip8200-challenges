import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanState

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false

/-!
# The scan states of the scalar-SWAR guard

The five constants stay on the stack for the whole scan, so a loop state is
those five under the running scalar, offset and accumulator.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec PatternedSwar

/-- The stepper writes `*`; the recurrence writes `UInt256.mul`. -/
@[simp] theorem mul_eq (a b : UInt256) : a * b = UInt256.mul a b := rfl

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod
  Challenge.EvmProof.Word.word_toNat_ofNat

def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

/-! Only these projections of the initial state are ever unfolded, so `simp`
never normalizes the 5305-byte array. -/

@[simp] theorem initialState_code (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).executionEnv.code = code := rfl

@[simp] theorem initialState_halt (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).halt = .Running := rfl

@[simp] theorem initialState_memory (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).memory = ByteArray.empty := rfl

@[simp] theorem initialState_activeWords (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).activeWords = 0 := rfl

attribute [local simp] Challenge.Ripemd160.initialState_stack
  Challenge.Ripemd160.initialState_pc
  Challenge.Ripemd160.initialState_calldata

/-- The constants the setup leaves below the working values. -/
def frame : List UInt256 := [P7, M, m7, P, m8]

/-- The accumulator after `k` words, as the guard builds it. -/
def scanAcc (input : ByteArray) : Nat → UInt256
  | 0 => 0
  | k + 1 =>
      UInt256.lor (scanAcc input k)
        (UInt256.xor (MachineState.readWord input (32 * k)) (guardWord k))

/-- At the head of the scan with `k` words folded in. -/
def loopState (input : ByteArray) (k : Nat) (a : UInt256) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5144
    stack := UInt256.ofNat (scalarAt k) :: UInt256.ofNat (32 * k) :: a :: frame }

/-- After the expected word is derived and any correction applied.  A
straddling word has already bumped the scalar by eleven, so it is explicit. -/
def compareState (input : ByteArray) (k s : Nat) (a : UInt256) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5170
    stack := guardWord k :: UInt256.mul M (UInt256.ofNat (scalarAt k)) ::
      UInt256.ofNat s :: UInt256.ofNat (32 * k) :: a :: frame }

/-- At the head of the correction block, for a straddling offset. -/
def straddleState (input : ByteArray) (k : Nat) (a : UInt256) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5264
    stack := rawWord k :: UInt256.mul M (UInt256.ofNat (scalarAt k)) ::
      UInt256.ofNat (scalarAt k) :: UInt256.ofNat (32 * k) :: a :: frame }

/-- After the thirty-one words, at the padded tail. -/
def tailState (input : ByteArray) (a : UInt256) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5203
    stack := UInt256.ofNat (scalarAt 31) :: UInt256.ofNat 992 :: a :: frame }

/-- Scanner values retained below the branch condition on the hot hit path. -/
def retainedStack (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat (scalarAt 31), UInt256.ofNat 992, scanAcc input 31, P7, M, m7, P, m8]

/-- The stub jumps here, and the guard answers or falls through.  -/
def patternedEntry (input : ByteArray) : State := atPC input 5005

def hitState (input : ByteArray) : State :=
  { atPC input 5226 with stack := retainedStack input }
def fallbackState (input : ByteArray) : State := atPC input 1006

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray := storeWord ByteArray.empty 0 paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5252
    stack := retainedStack input
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

theorem run_setup (input : ByteArray) :
    run setupPath (atPC input 5005) = some (loopState input 0 0) := by
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := rfl
  simp (config := { maxSteps := 400000 })
    [hzero, setupPath, opAt, pushAt, wfOp, atPC, loopState, frame, scanAcc, scalarAt,
      P7, P, m7, m8, M,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat]

/-! ### Arithmetic the scan needs on its offset -/

theorem land_ff (n : Nat) (hn : n < 2 ^ 256) :
    UInt256.land (UInt256.ofNat 255) (UInt256.ofNat n) = UInt256.ofNat (n % 256) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (by norm_num : 255 < 2 ^ 256),
    Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt n (by decide)) (by norm_num))]
  rw [Nat.and_comm, show 255 = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]

theorem straddle_iff (k : Nat) (hk : k < 31) :
    UInt256.land (UInt256.ofNat 255) (UInt256.ofNat (32 * k)) = UInt256.ofNat 224 ↔
      (32 * k) % 256 = 224 := by
  rw [land_ff _ (by omega)]
  constructor
  · intro h
    have := congrArg UInt256.toNat h
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by norm_num)),
      Nat.mod_eq_of_lt (by norm_num : 224 < 2 ^ 256)] at this
    exact this
  · intro h; rw [h]

/-! ### Deriving one expected word -/

set_option maxHeartbeats 80000000 in
theorem run_word_regular (input : ByteArray) (k : Nat) (a : UInt256) (hk : k < 31)
    (h : ¬ ((32 * k) % 256 = 224)) :
    run wordPath (loopState input k a) = some (compareState input k (scalarAt k) a) := by
  have hval : ((UInt256.ofNat 255).land (UInt256.ofNat (32 * k))).toNat
      = (32 * k) % 256 := by
    rw [land_ff _ (by omega), Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by norm_num))]
  have hcond : ¬ UInt256.isTrue ((UInt256.ofNat 224).eq
      ((UInt256.ofNat 255).land (UInt256.ofNat (32 * k)))) := by
    unfold UInt256.isTrue UInt256.eq
    rw [if_neg (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 224 < 2 ^ 256), hval]
      exact fun he => h he.symm)]
    decide
  have hk224 : ¬ ((32 * k) % 256 == 224) = true := by simpa using h
  simp (config := { maxSteps := 800000 })
    [wordPath, opAt, pushAt, wfOp, loopState, compareState, frame, rawWord,
      guardWord, hk224, hcond,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat]

set_option maxHeartbeats 80000000 in
theorem run_word_straddle (input : ByteArray) (k : Nat) (a : UInt256) (hk : k < 31)
    (h : (32 * k) % 256 = 224) :
    run wordPath (loopState input k a) = some (straddleState input k a) := by
  have hval : ((UInt256.ofNat 255).land (UInt256.ofNat (32 * k))).toNat
      = (32 * k) % 256 := by
    rw [land_ff _ (by omega), Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by norm_num))]
  have hcond : UInt256.isTrue ((UInt256.ofNat 224).eq
      ((UInt256.ofNat 255).land (UInt256.ofNat (32 * k)))) := by
    unfold UInt256.isTrue UInt256.eq
    rw [if_pos (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 224 < 2 ^ 256), hval, h])]
    decide
  have hdest : Decode.isValidJumpDest submissionBytecode 5264 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2989 (by rfl)
  have hdestN : Decode.isValidJumpDest submissionBytecode
      (UInt256.ofNat 5264).toNat = true := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by norm_num : 5264 < 2 ^ 256)]
    exact hdest
  have hdestL : Decode.isValidJumpDest submissionBytecode
      ((5264 : UInt256)).toNat = true := by
    rw [show ((5264 : UInt256)).toNat = 5264 from by decide]
    exact hdest
  simp (config := { maxSteps := 800000 })
    [wordPath, opAt, pushAt, wfOp, loopState, straddleState, frame, rawWord,
      hcond, hdest, hdestN, hdestL,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat]

def sound (path : List Located) {s t : State}
    (h : run path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) : GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    path hcode hfork h hrun hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
