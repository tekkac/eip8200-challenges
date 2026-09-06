import Challenge.Modexp.Submission.Proofs.Bytecode.WordCorrect
import Challenge.EvmProof.Meter
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-!
# Exact gas use of the one-word MODEXP path

The path is value-independent.  Its only input-dependent loop counts are the
declared base and exponent byte lengths; the final memory expansion to
`0x1800` is included in the constant term.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordGas

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Word
open WordLoops
open WordExit
open WordCorrect

private theorem blockCost_of_static
    {artifact : Challenge.EvmProof.ProgramArtifact} {fork : Fork}
    (path : List (Challenge.EvmProof.Stepper.Located artifact fork)) {s t : State}
    (work : Nat)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = fork)
    (hfree : ∀ located ∈ path,
      Challenge.EvmProof.Meter.CopyFree located.instruction)
    (hcost : Challenge.EvmProof.Meter.runLocatedBlockStaticCost path = work)
    (hactive : s.activeWords = t.activeWords) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost path s = work := by
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    path work hresult hfork hfree hcost
  rw [hactive] at hmeter
  omega

theorem gasSteps_start_cost (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodpos : 0 < modulusValue input) :
    (gasSteps_start input hvalid hmsize hword hmodpos).cost = 41 := by
  have hmodlt : modulusValue input < 2 ^ 256 :=
    (Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input
      (modulusOffset input) (modulusSize input)).trans_le (by
        have hp := pow_le_pow_right₀ (by omega : 1 ≤ (256 : Nat)) hword
        exact hp.trans (by norm_num))
  have hload := blockCost_of_static startLoadPath 31
    (run_startLoad input hvalid hmsize hword) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hjump := blockCost_of_static startJumpPath 10
    (run_startJump_nonzero input hmodpos hmodlt) (by rfl)
    (by decide) (by rfl) (by rfl)
  unfold gasSteps_start
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

@[simp] theorem gasSteps_baseSetup_cost (input : ByteArray) :
    (gasSteps_baseSetup input).cost = 5 := by
  have hmeter := blockCost_of_static baseSetupPath 5
    (run_baseSetup input) (by rfl)
    (by decide) (by rfl) (by rfl)
  unfold gasSteps_baseSetup
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  exact hmeter

theorem gasSteps_baseIteration_cost (input : ByteArray) (i : Nat)
    (base : UInt256) (hvalid : ValidInput input) (hi : i < baseSize input) :
    (gasSteps_baseIteration input i base hvalid hi).cost = 132 := by
  have hguard := blockCost_of_static baseGuardPath 26
    (run_baseGuard input i base hvalid hi) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hcall := blockCost_of_static baseCallPath 28
    (run_baseCall input i base hvalid hi) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hcap : (baseRest input i base).length < 1017 := by
    simp [baseRest, callerRest]
  have hhelper := blockCost_of_static Accessors.calldataBytePath 30
    (Accessors.run_calldataByte (baseLoopState input i base)
      (UInt256.ofNat (96 + i)) 0 562 (baseRest input i base) hcap rfl rfl
      (by decide)) (by rfl)
    (by decide) (by rfl) (by rfl)
  have htail := blockCost_of_static baseTailPath 48
    (run_baseTail input i base hvalid hi) (by rfl)
    (by decide) (by rfl) (by rfl)
  have htail' : Challenge.EvmProof.Stepper.runLocatedBlockCost baseTailPath
      (Accessors.calldataByteReturned (baseLoopState input i base)
        (UInt256.ofNat (96 + i)) 562 (baseRest input i base)) = 48 := by
    simpa [baseReturnedState, Accessors.calldataByteReturned] using htail
  unfold gasSteps_baseIteration
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost,
    Accessors.gasSteps_calldataByte]
  omega

theorem gasSteps_baseLoop_cost (input : ByteArray) (hvalid : ValidInput input) :
    (gasSteps_baseLoop input hvalid).cost = 132 * baseSize input := by
  unfold gasSteps_baseLoop
  have h := Challenge.EvmProof.GasSteps.iterateBounded_cost_of_const
    (count := baseSize input) (cost := 132) (body := fun i hi =>
      gasSteps_baseIteration input i (baseAfter input i) hvalid hi) (by
        intro i hi
        exact gasSteps_baseIteration_cost input i (baseAfter input i) hvalid hi)
  simpa [Nat.mul_comm] using h

theorem gasSteps_baseFinish_cost (input : ByteArray) (base : UInt256)
    (hvalid : ValidInput input) (hword : modulusSize input ≤ 32) :
    (gasSteps_baseFinish input base hvalid hword).cost = 42 := by
  have hguard := blockCost_of_static baseGuardPath 26
    (run_baseFinishGuard input base hvalid) (by rfl)
    (by decide) (by rfl) (by rfl)
  have htail := blockCost_of_static baseFinishTailPath 16
    (run_baseFinishTail input base hvalid hword) (by rfl)
    (by decide) (by rfl) (by rfl)
  unfold gasSteps_baseFinish
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

theorem gasSteps_expEnter_cost (input : ByteArray) (i : Nat)
    (acc base : UInt256) (hvalid : ValidInput input)
    (hi : i < exponentSize input) :
    (gasSteps_expEnter input i acc base hvalid hi).cost = 48 := by
  have hguard := blockCost_of_static expGuardPath 26
    (run_expGuard input i acc base hvalid hi) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hload := blockCost_of_static expLoadPath 22
    (run_expLoad input i acc base hvalid hi) (by rfl)
    (by decide) (by rfl) (by rfl)
  unfold gasSteps_expEnter
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

theorem gasSteps_bitCopy0_cost (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    (gasSteps_bitCopy0 input outer byte offset acc base).cost = 81 := by
  have hdecode := blockCost_of_static Unroll0.bitDecodePath0 15
    (Unroll0.run_bitDecode input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hsquare := blockCost_of_static Unroll0.bitSquarePath0 17
    (Unroll0.run_bitSquare input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hmask := blockCost_of_static Unroll0.bitMaskPath0 8
    (Unroll0.run_bitMask input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hproduct := blockCost_of_static Unroll0.bitProductPath0 17
    (Unroll0.run_bitProduct input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hchoose := blockCost_of_static Unroll0.bitChoosePath0 15
    (Unroll0.run_bitChoose input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hadvance := blockCost_of_static Unroll0.bitAdvancePath0 9
    (Unroll0.run_bitAdvance input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  unfold gasSteps_bitCopy0
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

theorem gasSteps_bitCopy1_cost (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    (gasSteps_bitCopy1 input outer byte offset acc base).cost = 81 := by
  have hdecode := blockCost_of_static Unroll1.bitDecodePath1 15
    (Unroll1.run_bitDecode input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hsquare := blockCost_of_static Unroll1.bitSquarePath1 17
    (Unroll1.run_bitSquare input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hmask := blockCost_of_static Unroll1.bitMaskPath1 8
    (Unroll1.run_bitMask input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hproduct := blockCost_of_static Unroll1.bitProductPath1 17
    (Unroll1.run_bitProduct input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hchoose := blockCost_of_static Unroll1.bitChoosePath1 15
    (Unroll1.run_bitChoose input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hadvance := blockCost_of_static Unroll1.bitAdvancePath1 9
    (Unroll1.run_bitAdvance input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  unfold gasSteps_bitCopy1
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

theorem gasSteps_bitCopy2_cost (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    (gasSteps_bitCopy2 input outer byte offset acc base).cost = 81 := by
  have hdecode := blockCost_of_static Unroll2.bitDecodePath2 15
    (Unroll2.run_bitDecode input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hsquare := blockCost_of_static Unroll2.bitSquarePath2 17
    (Unroll2.run_bitSquare input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hmask := blockCost_of_static Unroll2.bitMaskPath2 8
    (Unroll2.run_bitMask input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hproduct := blockCost_of_static Unroll2.bitProductPath2 17
    (Unroll2.run_bitProduct input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hchoose := blockCost_of_static Unroll2.bitChoosePath2 15
    (Unroll2.run_bitChoose input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hadvance := blockCost_of_static Unroll2.bitAdvancePath2 9
    (Unroll2.run_bitAdvance input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  unfold gasSteps_bitCopy2
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

theorem gasSteps_bitCopy3_cost (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    (gasSteps_bitCopy3 input outer byte offset acc base).cost = 81 := by
  have hdecode := blockCost_of_static Unroll3.bitDecodePath3 15
    (Unroll3.run_bitDecode input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hsquare := blockCost_of_static Unroll3.bitSquarePath3 17
    (Unroll3.run_bitSquare input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hmask := blockCost_of_static Unroll3.bitMaskPath3 8
    (Unroll3.run_bitMask input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hproduct := blockCost_of_static Unroll3.bitProductPath3 17
    (Unroll3.run_bitProduct input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hchoose := blockCost_of_static Unroll3.bitChoosePath3 15
    (Unroll3.run_bitChoose input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hadvance := blockCost_of_static Unroll3.bitAdvancePath3 9
    (Unroll3.run_bitAdvance input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  unfold gasSteps_bitCopy3
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

theorem gasSteps_bitCopy4_cost (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    (gasSteps_bitCopy4 input outer byte offset acc base).cost = 81 := by
  have hdecode := blockCost_of_static Unroll4.bitDecodePath4 15
    (Unroll4.run_bitDecode input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hsquare := blockCost_of_static Unroll4.bitSquarePath4 17
    (Unroll4.run_bitSquare input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hmask := blockCost_of_static Unroll4.bitMaskPath4 8
    (Unroll4.run_bitMask input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hproduct := blockCost_of_static Unroll4.bitProductPath4 17
    (Unroll4.run_bitProduct input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hchoose := blockCost_of_static Unroll4.bitChoosePath4 15
    (Unroll4.run_bitChoose input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hadvance := blockCost_of_static Unroll4.bitAdvancePath4 9
    (Unroll4.run_bitAdvance input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  unfold gasSteps_bitCopy4
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

theorem gasSteps_bitCopy5_cost (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    (gasSteps_bitCopy5 input outer byte offset acc base).cost = 81 := by
  have hdecode := blockCost_of_static Unroll5.bitDecodePath5 15
    (Unroll5.run_bitDecode input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hsquare := blockCost_of_static Unroll5.bitSquarePath5 17
    (Unroll5.run_bitSquare input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hmask := blockCost_of_static Unroll5.bitMaskPath5 8
    (Unroll5.run_bitMask input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hproduct := blockCost_of_static Unroll5.bitProductPath5 17
    (Unroll5.run_bitProduct input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hchoose := blockCost_of_static Unroll5.bitChoosePath5 15
    (Unroll5.run_bitChoose input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hadvance := blockCost_of_static Unroll5.bitAdvancePath5 9
    (Unroll5.run_bitAdvance input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  unfold gasSteps_bitCopy5
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

theorem gasSteps_bitCopy6_cost (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    (gasSteps_bitCopy6 input outer byte offset acc base).cost = 81 := by
  have hdecode := blockCost_of_static Unroll6.bitDecodePath6 15
    (Unroll6.run_bitDecode input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hsquare := blockCost_of_static Unroll6.bitSquarePath6 17
    (Unroll6.run_bitSquare input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hmask := blockCost_of_static Unroll6.bitMaskPath6 8
    (Unroll6.run_bitMask input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hproduct := blockCost_of_static Unroll6.bitProductPath6 17
    (Unroll6.run_bitProduct input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hchoose := blockCost_of_static Unroll6.bitChoosePath6 15
    (Unroll6.run_bitChoose input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hadvance := blockCost_of_static Unroll6.bitAdvancePath6 9
    (Unroll6.run_bitAdvance input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  unfold gasSteps_bitCopy6
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

theorem gasSteps_bitCopy7_cost (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    (gasSteps_bitCopy7 input outer byte offset acc base).cost = 81 := by
  have hdecode := blockCost_of_static Unroll7.bitDecodePath7 15
    (Unroll7.run_bitDecode input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hsquare := blockCost_of_static Unroll7.bitSquarePath7 17
    (Unroll7.run_bitSquare input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hmask := blockCost_of_static Unroll7.bitMaskPath7 8
    (Unroll7.run_bitMask input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hproduct := blockCost_of_static Unroll7.bitProductPath7 17
    (Unroll7.run_bitProduct input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hchoose := blockCost_of_static Unroll7.bitChoosePath7 15
    (Unroll7.run_bitChoose input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hadvance := blockCost_of_static Unroll7.bitAdvancePath7 9
    (Unroll7.run_bitAdvance input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  unfold gasSteps_bitCopy7
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

theorem gasSteps_bitLoop_cost (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    (gasSteps_bitLoop input outer byte offset acc base).cost = 661 := by
  have hentry := blockCost_of_static bitEntryPath 4
    (run_bitEntry input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hjump := blockCost_of_static bitJumpPath 8
    (run_bitJump input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hhead := blockCost_of_static bitHeadPath 1
    (run_bitHead input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hcopy0 := gasSteps_bitCopy0_cost input outer byte offset
    (bitAfter input byte base 0 acc) base
  have hcopy1 := gasSteps_bitCopy1_cost input outer byte offset
    (bitAfter input byte base 1 acc) base
  have hcopy2 := gasSteps_bitCopy2_cost input outer byte offset
    (bitAfter input byte base 2 acc) base
  have hcopy3 := gasSteps_bitCopy3_cost input outer byte offset
    (bitAfter input byte base 3 acc) base
  have hcopy4 := gasSteps_bitCopy4_cost input outer byte offset
    (bitAfter input byte base 4 acc) base
  have hcopy5 := gasSteps_bitCopy5_cost input outer byte offset
    (bitAfter input byte base 5 acc) base
  have hcopy6 := gasSteps_bitCopy6_cost input outer byte offset
    (bitAfter input byte base 6 acc) base
  have hcopy7 := gasSteps_bitCopy7_cost input outer byte offset
    (bitAfter input byte base 7 acc) base
  unfold gasSteps_bitLoop
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

theorem gasSteps_bitFinish_cost (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) (hvalid : ValidInput input)
    (houter : outer < exponentSize input) :
    (gasSteps_bitFinish input outer byte offset acc base hvalid houter).cost = 35 := by
  have hexit := blockCost_of_static bitExitPath 11
    (run_bitExit input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have htail := blockCost_of_static bitFinishTailPath 24
    (run_bitFinishTail input outer byte offset acc base hvalid houter) (by rfl)
    (by decide) (by rfl) (by rfl)
  unfold gasSteps_bitFinish
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

theorem gasSteps_expIteration_cost (input : ByteArray) (i : Nat)
    (acc base : UInt256) (hvalid : ValidInput input)
    (hi : i < exponentSize input) :
    (gasSteps_expIteration input i acc base hvalid hi).cost = 744 := by
  simp [gasSteps_expIteration, gasSteps_expEnter_cost, gasSteps_bitLoop_cost,
    gasSteps_bitFinish_cost]

theorem gasSteps_expLoop_cost (input : ByteArray) (acc base : UInt256)
    (hvalid : ValidInput input) :
    (gasSteps_expLoop input acc base hvalid).cost = 744 * exponentSize input := by
  unfold gasSteps_expLoop
  have h := Challenge.EvmProof.GasSteps.iterateBounded_cost_of_const
    (count := exponentSize input) (cost := 744) (body := fun i hi =>
      gasSteps_expIteration input i (expAfter input base i acc) base hvalid hi) (by
        intro i hi
        exact gasSteps_expIteration_cost input i (expAfter input base i acc)
          base hvalid hi)
  simpa [Nat.mul_comm] using h

theorem gasSteps_expFinish_cost (input : ByteArray) (acc base : UInt256)
    (hvalid : ValidInput input) (hword : modulusSize input ≤ 32) :
    (gasSteps_expFinish input acc base hvalid hword).cost = 65 := by
  have hguard := blockCost_of_static expGuardPath 26
    (run_expFinishGuard input acc base hvalid) (by rfl)
    (by decide) (by rfl) (by rfl)
  have htail := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    expFinishTailPath 36
    (run_expFinishTail input acc base hvalid hword) (by rfl)
    (by decide) (by rfl)
  have hreturned : MachineState.activeWordsAfter 1 0
      (modulusSize input) = 1 := by
    unfold MachineState.activeWordsAfter
    split
    · rfl
    · have hdiv : (modulusSize input - 1) / 32 = 0 := by omega
      dsimp
      rw [show 0 + modulusSize input - 1 = modulusSize input - 1 by omega,
        hdiv]
      decide
  have hstored : MachineState.activeWordsAfter 0 0 32 = 1 := by decide
  have hfinal : (wordFinalState input acc base).activeWords.toNat = 1 := by
    change (UInt256.ofNat (MachineState.activeWordsAfter
      (MachineState.activeWordsAfter 0 0 32) 0
        (modulusSize input))).toNat = 1
    rw [hstored, hreturned]
    decide
  rw [show (expFinishDispatchState input acc base).activeWords.toNat = 0 by rfl,
    hfinal] at htail
  norm_num [MachineState.memCost] at htail
  unfold gasSteps_expFinish
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

theorem gasSteps_zeroModulus_cost (input : ByteArray)
    (hvalid : ValidInput input) (hmsize : 0 < modulusSize input)
    (hword : modulusSize input ≤ 32) (hmodulus : modulusValue input = 0) :
    (gasSteps_zeroModulus input hvalid hmsize hword hmodulus).cost = 50 := by
  have hload := blockCost_of_static startLoadPath 31
    (run_startLoad input hvalid hmsize hword) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hjump := blockCost_of_static startJumpPath 10
    (run_startJump_zero input hmodulus) (by rfl)
    (by decide) (by rfl) (by rfl)
  have htail := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    zeroTailPath 6 (run_zeroTail input hvalid hmodulus) (by rfl)
      (by decide) (by decide)
  have hfinal : (zeroModulusFinalState input).activeWords.toNat = 1 := by
    change (UInt256.ofNat
      (MachineState.activeWordsAfter 0 0 (modulusSize input))).toNat = 1
    have hactive : MachineState.activeWordsAfter 0 0
        (modulusSize input) = 1 := by
      unfold MachineState.activeWordsAfter
      split
      · next hzero => omega
      · next hnonzero =>
        have hdiv : (modulusSize input - 1) / 32 = 0 := by omega
        dsimp
        rw [show 0 + modulusSize input - 1 =
          modulusSize input - 1 by omega, hdiv]
        decide
    rw [hactive]
    decide
  rw [show (zeroDispatchState input).activeWords.toNat = 0 by rfl,
    hfinal] at htail
  norm_num [MachineState.memCost] at htail
  unfold gasSteps_zeroModulus
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  rw [hload, hjump]
  omega

theorem gasSteps_zeroModulus_total_cost_after_header (input : ByteArray)
    (hvalid : ValidInput input) (hmsize : 0 < modulusSize input)
    (hword : modulusSize input ≤ 32) (hmodulus : modulusValue input = 0)
    (entry : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (Main.trampolineState input 1196)) :
    (gasSteps_zeroModulus_total input hvalid hmsize hword hmodulus entry).cost =
      (Main.gasSteps_header input hvalid entry).cost + 140 := by
  unfold gasSteps_zeroModulus_total
  simp only [Challenge.EvmProof.GasSteps.trans_cost]
  rw [Dispatch.gasSteps_wordEntry_cost input hvalid hmsize hword,
    gasSteps_zeroModulus_cost input hvalid hmsize hword hmodulus]

def wordGas (input : ByteArray) : Nat :=
  283 + 132 * baseSize input + 744 * exponentSize input

end Challenge.Modexp.Submission.Proofs.Bytecode.WordGas
