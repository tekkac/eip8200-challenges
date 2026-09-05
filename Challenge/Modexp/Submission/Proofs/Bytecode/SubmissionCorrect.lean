import Challenge.Modexp.ProofSupport.Bytecode
import Challenge.Modexp.Submission.Proofs.Bytecode.BigZeroCorrect
import Challenge.Modexp.Submission.Proofs.Bytecode.WordGas
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
/-! # End-to-end correctness and exact gas for the submission MODEXP bytecode -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.SubmissionCorrect

open EvmSemantics
open EvmSemantics.EVM

@[simp] theorem mulWordProgress_callStack (current : State)
    (word a b out modulus : UInt256) (count i j : Nat)
    (returnDest : UInt256) (rest : List UInt256) :
    (BigMul.mulWordProgress current word a b out modulus count i returnDest rest
      j).callStack = current.callStack := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp [BigMul.mulWordProgress, BigMul.mulWordAfterDouble,
        BigMul.mulWordAfterAdd, BigMul.mulInnerState, BigHelpers.addReturned, ih]

@[simp] theorem mulOuterProgress_callStack (current : State)
    (a b out modulus : UInt256) (count i : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (BigMul.mulOuterProgress current a b out modulus count returnDest rest
      i).callStack = current.callStack := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp [BigMul.mulOuterProgress, BigMul.mulLoadedState, ih]

@[simp] theorem mulResult_callStack (s : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (BigExponent.mulResult s a b out modulus count returnDest rest).callStack =
      s.callStack := by
  simp [BigExponent.mulResult, BigMul.mulReturned, BigMul.mulAfterCopy,
    BigMul.mulAfterClear]

@[simp] theorem squareReturned_callStack (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (BigExponent.squareReturned s accumulatorWord count b e m baseOff expOff
      i j offset byte rest).callStack = s.callStack := by
  simp [BigExponent.squareReturned, BigExponent.innerBody,
    BigExponent.innerLoop]

@[simp] theorem copiedSquare_callStack (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (BigExponent.copiedSquare s accumulatorWord count b e m baseOff expOff
      i j offset byte rest).callStack = s.callStack := by
  simp [BigExponent.copiedSquare, BigHelpers.copyReturned]

@[simp] theorem productReturned_callStack (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (BigExponent.productReturned s accumulatorWord count b e m baseOff expOff
      i j offset byte rest).callStack = s.callStack := by
  simp [BigExponent.productReturned]

@[simp] theorem selectProgress_callStack (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j k : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (BigExponent.selectProgress s accumulatorWord count b e m baseOff expOff
      i j offset byte rest k).callStack = s.callStack := by
  simp [BigExponent.selectProgress]

@[simp] theorem exponentBitProgress_callStack (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (BigExponent.exponentBitProgress s accumulatorWord count b e m baseOff
      expOff i offset byte rest j).callStack = s.callStack := by
  induction j with
  | zero => rfl
  | succ j ih => simp [BigExponent.exponentBitProgress, ih]

@[simp] theorem exponentByteProgress_callStack (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i : Nat)
    (rest : List UInt256) :
    (BigExponent.exponentByteProgress s accumulatorWord count b e m baseOff
      expOff rest i).callStack = s.callStack := by
  induction i with
  | zero => rfl
  | succ i ih => simp [BigExponent.exponentByteProgress, ih]

@[simp] theorem baseBitProgress_callStack (count : Nat) (byte : UInt256)
    (j : Nat) (s : State) :
    (BigBase.bitProgress count byte j s).callStack = s.callStack := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp [BigBase.bitProgress, BigHelpers.addReturned, ih]

@[simp] theorem baseProgress_callStack (count baseOff i : Nat) (s : State) :
    (BigBase.baseProgress count baseOff i s).callStack = s.callStack := by
  induction i with
  | zero => rfl
  | succ i ih => simp [BigBase.baseProgress, ih]

@[simp] theorem setupState_callStack (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (BigComplete.setupState s b e m baseOff expOff modOff returnDest
      rest).callStack = s.callStack := by
  rfl

@[simp] theorem serializeProgress_callStack (s : State) (m k : Nat) :
    (BigSerialize.serializeProgress s m k).callStack = s.callStack := by
  rfl

@[simp] theorem baseState_callStack (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (BigComplete.baseState s b e m baseOff expOff modOff returnDest
      rest).callStack = s.callStack := by
  simp [BigComplete.baseState, BigBase.baseLoopEntry,
    BigBase.afterClearDouble, BigHelpers.clearReturned,
    BigModulus.scanNonzero]

@[simp] theorem exponentState_callStack (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (BigComplete.exponentState s b e m baseOff expOff modOff returnDest
      rest).callStack = s.callStack := by
  simp [BigComplete.exponentState, BigBaseLoop.initialAccumulator,
    BigBaseLoop.baseConvertedExit, BigBase.outerExit, BigBase.outerLoop,
    BigHelpers.addReturned]

@[simp] theorem exponentProgressState_callStack (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (BigComplete.exponentProgressState s b e m baseOff expOff modOff returnDest
      rest).callStack = s.callStack := by
  simp [BigComplete.exponentProgressState]

@[simp] theorem completedState_callStack (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (BigComplete.completedState s b e m baseOff expOff modOff returnDest
      rest).callStack = s.callStack := by
  simp [BigComplete.completedState, BigSerialize.bigReturned,
    BigSerialize.serializeProgress]

@[simp] theorem zeroFinalState_callStack (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (BigZeroCorrect.zeroFinalState s b e m baseOff expOff modOff returnDest
      rest).callStack = s.callStack := by
  simp [BigZeroCorrect.zeroFinalState, BigModulus.scanZeroFinal,
    setupState_callStack]

@[simp] theorem completedState_isDone (input : ByteArray)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (BigComplete.completedState (Main.headerState input) b e m baseOff expOff
      modOff returnDest rest).isDone = true := by
  simp [State.isDone, State.isHalted, State.isRunning,
    BigComplete.completedState, BigSerialize.bigReturned, Main.headerState,
    initialState]

@[simp] theorem zeroFinalState_isDone (input : ByteArray)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (BigZeroCorrect.zeroFinalState (Main.headerState input) b e m baseOff
      expOff modOff returnDest rest).isDone = true := by
  simp [State.isDone, State.isHalted, State.isRunning,
    BigZeroCorrect.zeroFinalState, BigModulus.scanZeroFinal, Main.headerState,
    initialState]

def bigRest (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat (Word.modulusOffset input), UInt256.ofNat (Word.expOffset input),
    UInt256.ofNat (modulusSize input), UInt256.ofNat (exponentSize input),
    UInt256.ofNat (baseSize input)]

def bigReturnDest : UInt256 := UInt256.ofNat 1283

def bigCompletedState (input : ByteArray) : State :=
  BigComplete.completedState (Main.headerState input) (baseSize input)
    (exponentSize input) (modulusSize input) 96 (Word.expOffset input)
    (Word.modulusOffset input) bigReturnDest (bigRest input)

def bigZeroFinalState (input : ByteArray) : State :=
  BigZeroCorrect.zeroFinalState (Main.headerState input) (baseSize input)
    (exponentSize input) (modulusSize input) 96 (Word.expOffset input)
    (Word.modulusOffset input) bigReturnDest (bigRest input)

private def certifiedBigNonzeroTotal (input : ByteArray)
    (hvalid : ValidInput input) (hbig : 32 < modulusSize input)
    (hmodulusPos : 0 < Word.modulusValue input)
    (entry : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (Main.trampolineState input 1196)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (bigCompletedState input) := by
  have hb := hvalid.2.1
  have he := hvalid.2.2.1
  have hm := hvalid.2.2.2
  have hmodOff : Word.modulusOffset input < 2 ^ 256 := by
    simp only [Word.modulusOffset, Word.expOffset]
    omega
  have hinputFit : Word.modulusOffset input + modulusSize input ≤ 2 ^ 256 := by
    simp only [Word.modulusOffset, Word.expOffset]
    omega
  have hor : BigComplete.modulusOr (Main.headerState input) (baseSize input)
      (exponentSize input) (modulusSize input) 96 (Word.expOffset input)
      (Word.modulusOffset input) bigReturnDest (bigRest input) ≠ 0 := by
    intro hz
    have := (BigZeroCorrect.modulusOr_eq_zero_iff input bigReturnDest
      (bigRest input) hvalid).1 hz
    omega
  have hbase : baseSize input < 2 ^ 256 := by omega
  have hbaseFit : 96 + baseSize input < 2 ^ 256 := by omega
  have hexp : exponentSize input < 2 ^ 256 := by omega
  have hexpFit : Word.expOffset input + exponentSize input < 2 ^ 256 := by
    simp only [Word.expOffset]
    omega
  have hcap : (bigRest input).length < 960 := by simp [bigRest]
  have hcode : (Main.headerState input).executionEnv.code = submissionBytecode := rfl
  have hfork : (Main.headerState input).fork = .Osaka := rfl
  have hrun : (Main.headerState input).halt = .Running := rfl
  let hcore := BigComplete.gasSteps_nonzero (Main.headerState input)
    (baseSize input) (exponentSize input) (modulusSize input) 96
    (Word.expOffset input) (Word.modulusOffset input) bigReturnDest
    (bigRest input) hm hmodOff hinputFit hbase hbaseFit hexp hexpFit hcap hor
    hcode hfork hrun deployAddress_not_precompile
  let hcore' : Challenge.EvmProof.GasSteps (BigDispatch.bigEntryState input)
      (bigCompletedState input) := Challenge.EvmProof.GasSteps.cast hcore
        (by simp [BigDispatch.bigEntryState, BigSetup.setupEntry, bigRest,
          bigReturnDest, Word.expOffset, Word.modulusOffset, Nat.add_assoc])
        (by rfl)
  have hpositive : 0 < modulusSize input := by omega
  let total := ((Main.gasSteps_header input hvalid entry).trans
    (BigDispatch.gasSteps_bigEntry input hvalid hpositive hbig)).trans hcore'
  exact total

def gasSteps_bigNonzeroTotal (input : ByteArray) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input) (hmodulusPos : 0 < Word.modulusValue input)
    (entry : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (Main.trampolineState input 1196)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (bigCompletedState input) :=
  certifiedBigNonzeroTotal input hvalid hbig hmodulusPos entry

private def certifiedBigZeroTotal (input : ByteArray) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input) (hmodulus : Word.modulusValue input = 0)
    (entry : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (Main.trampolineState input 1196)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (bigZeroFinalState input) := by
  have hb := hvalid.2.1
  have he := hvalid.2.2.1
  have hm := hvalid.2.2.2
  have hmodOff : Word.modulusOffset input < 2 ^ 256 := by
    simp only [Word.modulusOffset, Word.expOffset]
    omega
  have hinputFit : Word.modulusOffset input + modulusSize input ≤ 2 ^ 256 := by
    simp only [Word.modulusOffset, Word.expOffset]
    omega
  have hor : BigComplete.modulusOr (Main.headerState input) (baseSize input)
      (exponentSize input) (modulusSize input) 96 (Word.expOffset input)
      (Word.modulusOffset input) bigReturnDest (bigRest input) = 0 :=
    (BigZeroCorrect.modulusOr_eq_zero_iff input bigReturnDest (bigRest input)
      hvalid).2 hmodulus
  have hcap : (bigRest input).length < 992 := by simp [bigRest]
  have hcode : (Main.headerState input).executionEnv.code = submissionBytecode := rfl
  have hfork : (Main.headerState input).fork = .Osaka := rfl
  have hrun : (Main.headerState input).halt = .Running := rfl
  let hcore := BigZeroCorrect.gasSteps_zero (Main.headerState input)
    (baseSize input) (exponentSize input) (modulusSize input) 96
    (Word.expOffset input) (Word.modulusOffset input) bigReturnDest
    (bigRest input) hm hmodOff hinputFit hcap hor hcode hfork hrun
    deployAddress_not_precompile
  let hcore' : Challenge.EvmProof.GasSteps (BigDispatch.bigEntryState input)
      (bigZeroFinalState input) := Challenge.EvmProof.GasSteps.cast hcore
        (by simp [BigDispatch.bigEntryState, BigSetup.setupEntry, bigRest,
          bigReturnDest, Word.expOffset, Word.modulusOffset, Nat.add_assoc])
        (by rfl)
  have hpositive : 0 < modulusSize input := by omega
  let total := ((Main.gasSteps_header input hvalid entry).trans
    (BigDispatch.gasSteps_bigEntry input hvalid hpositive hbig)).trans hcore'
  exact total

def gasSteps_bigZeroTotal (input : ByteArray) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input) (hmodulus : Word.modulusValue input = 0)
    (entry : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (Main.trampolineState input 1196)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (bigZeroFinalState input) :=
  certifiedBigZeroTotal input hvalid hbig hmodulus entry

def finalState (input : ByteArray) : State :=
  if modulusSize input = 0 then Dispatch.zeroSizeFinalState input
  else if modulusSize input ≤ 32 then
    if Word.modulusValue input = 0 then Word.zeroModulusFinalState input
    else WordExit.wordFinalState input (WordCorrect.wordResult input)
      (WordCorrect.wordBase input)
  else if Word.modulusValue input = 0 then bigZeroFinalState input
  else bigCompletedState input

def submissionGas (input : ByteArray) : Nat :=
  if modulusSize input = 0 then 61
  else if modulusSize input ≤ 32 then
    if Word.modulusValue input = 0 then 180 else WordGas.wordGas input
  else if Word.modulusValue input = 0 then
    131 + BigZeroCorrect.zeroWork (Limbs.limbCount (modulusSize input))
      (modulusSize input) +
      MachineState.memCost (bigZeroFinalState input).activeWords.toNat
  else
    131 + BigComplete.nonzeroWork (Limbs.limbCount (modulusSize input))
      (baseSize input) (exponentSize input) (modulusSize input) +
      MachineState.memCost (bigCompletedState input).activeWords.toNat

def gasSteps_submission (input : ByteArray) (hvalid : ValidInput input)
    (entry : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (Main.trampolineState input 1196)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (finalState input) := by
  by_cases hzeroSize : modulusSize input = 0
  · exact Challenge.EvmProof.GasSteps.cast
      (Dispatch.gasSteps_zeroSize_total input hvalid hzeroSize entry) rfl
      (by simp [finalState, hzeroSize])
  have hpositive : 0 < modulusSize input := by omega
  by_cases hword : modulusSize input ≤ 32
  · by_cases hzeroModulus : Word.modulusValue input = 0
    · exact Challenge.EvmProof.GasSteps.cast
        (Word.gasSteps_zeroModulus_total input hvalid hpositive hword
          hzeroModulus entry) rfl
        (by simp [finalState, hzeroSize, hword, hzeroModulus])
    · have hmodulusPos : 0 < Word.modulusValue input := by omega
      exact Challenge.EvmProof.GasSteps.cast
        (WordCorrect.gasSteps_wordNonzeroTotal input hvalid hpositive hword
          hmodulusPos entry) rfl
        (by simp [finalState, hzeroSize, hword, hzeroModulus])
  · have hbig : 32 < modulusSize input := by omega
    by_cases hzeroModulus : Word.modulusValue input = 0
    · exact Challenge.EvmProof.GasSteps.cast
        (gasSteps_bigZeroTotal input hvalid hbig hzeroModulus entry) rfl
        (by simp [finalState, hzeroSize, hword, hzeroModulus])
    · have hmodulusPos : 0 < Word.modulusValue input := by omega
      exact Challenge.EvmProof.GasSteps.cast
        (gasSteps_bigNonzeroTotal input hvalid hbig hmodulusPos entry) rfl
        (by simp [finalState, hzeroSize, hword, hzeroModulus])

@[simp] theorem finalState_isDone (input : ByteArray) :
    (finalState input).isDone = true := by
  by_cases hzeroSize : modulusSize input = 0
  · simp [finalState, hzeroSize]
  by_cases hword : modulusSize input ≤ 32
  · by_cases hzeroModulus : Word.modulusValue input = 0
    · simp [finalState, hzeroSize, hword, hzeroModulus]
    · simp [finalState, hzeroSize, hword, hzeroModulus]
  · by_cases hzeroModulus : Word.modulusValue input = 0
    · simp [finalState, hzeroSize, hword, hzeroModulus, bigZeroFinalState]
    · simp [finalState, hzeroSize, hword, hzeroModulus, bigCompletedState]

theorem finalState_result (input : ByteArray) (hvalid : ValidInput input) :
    (finalState input).toResult = .returned (spec input) := by
  by_cases hzeroSize : modulusSize input = 0
  · simpa [finalState, hzeroSize] using
      Dispatch.zeroSizeFinalState_result input hzeroSize
  have hpositive : 0 < modulusSize input := by omega
  by_cases hword : modulusSize input ≤ 32
  · by_cases hzeroModulus : Word.modulusValue input = 0
    · simpa [finalState, hzeroSize, hword, hzeroModulus] using
        Word.zeroModulusFinalState_result input hpositive hzeroModulus
    · have hmodulusPos : 0 < Word.modulusValue input := by omega
      simpa [finalState, hzeroSize, hword, hzeroModulus] using
        WordCorrect.wordFinalState_result input hvalid hpositive hword
          hmodulusPos
  · have hbig : 32 < modulusSize input := by omega
    by_cases hzeroModulus : Word.modulusValue input = 0
    · simpa [finalState, hzeroSize, hword, hzeroModulus, bigZeroFinalState] using
        BigZeroCorrect.zeroFinalState_result input bigReturnDest (bigRest input)
          hvalid hbig hzeroModulus
    · have hmodulusPos : 0 < Word.modulusValue input := by omega
      simpa [finalState, hzeroSize, hword, hzeroModulus, bigCompletedState] using
        BigSerializeCorrect.completedState_result input bigReturnDest
          (bigRest input) hvalid hbig hmodulusPos

@[simp] theorem withGas_initialState_zero (input : ByteArray) (gas : Nat) :
    Challenge.EvmProof.withGas (initialState submissionBytecode input 0) gas =
      initialState submissionBytecode input gas := by
  rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.SubmissionCorrect
