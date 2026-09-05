import Challenge.Modexp.Submission.Proofs.Memo.V2.State
import Challenge.Modexp.Submission.Proofs.Memo.V2.Paths
import Challenge.Modexp.Submission.Proofs.Memo.Step

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.V2.Trace

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Memo
open Logic Dispatch State Paths

theorem run_early_prefix (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock earlyPrefixPath (Main.trampolineState input 1473) =
      some (earlyJumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [earlyPrefixPath, earlyJumpState, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc2,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_early_jump_taken (input : ByteArray) (h : MachineState.readWord input 32 ≠ 0) :
    Challenge.EvmProof.Stepper.runLocated earlyJumpLocated (earlyJumpState input) =
      some (Main.trampolineState input 1553) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 1553 = true :=
    Artifact.isValidJumpDest_index 1087 (by rfl)
  have hpc : (earlyJumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1055 := by
    simp [earlyJumpState, initialState, PCs.pc2, Challenge.EvmProof.Word.word_toNat_ofNat]
  have hcond : UInt256.isTrue (MachineState.readWord input 32) := Step.isTrue_of_ne_zero h
  exact (Step.runLocated_jumpi_taken earlyJumpLocated rfl (earlyJumpState input) 1553 (MachineState.readWord input 32) [] hpc rfl (by simp) hcond rfl (by norm_num) hjump).trans rfl

theorem run_early_jump_not_taken (input : ByteArray) (h : MachineState.readWord input 32 = 0) :
    Challenge.EvmProof.Stepper.runLocated earlyJumpLocated (earlyJumpState input) =
      some (Main.trampolineState input 1481) := by
  have hpc : (earlyJumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1055 := by
    simp [earlyJumpState, initialState, PCs.pc2, Challenge.EvmProof.Word.word_toNat_ofNat]
  have hcond : ¬ UInt256.isTrue (MachineState.readWord input 32) := Step.not_isTrue_of_eq_zero h
  have hpcv : (earlyJumpState input).pc = UInt256.ofNat 1480 := rfl
  have hstack : (earlyJumpState input).stack = UInt256.ofNat 1553 :: MachineState.readWord input 32 :: [] := rfl
  have hrun := Step.runLocated_jumpi_not_taken earlyJumpLocated rfl (earlyJumpState input) 1553 (MachineState.readWord input 32) [] 1480 hpc hpcv (by decide) hstack (by decide) hcond
  exact hrun.trans rfl

theorem run_checks (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock checksPath (Main.trampolineState input 1481) =
      some (accState input 1531 (accRest input)) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [checksPath, accState, accRest, remainingChecks, guardDiff, scanDiff, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc2,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]


theorem run_branch_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated branchJumpLocated (State.branchJumpState input) =
      some (Main.trampolineState input 1540) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 1540 = true :=
    Artifact.isValidJumpDest_index 1075 (by rfl)
  have hpc : (State.branchJumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1072 := by
    simp [State.branchJumpState, initialState, PCs.pc2, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jumpi_taken branchJumpLocated rfl (State.branchJumpState input) 1540 (UInt256.ofNat 1) [] hpc rfl (by simp) Logic.isTrue_one rfl (by norm_num) hjump).trans rfl

theorem run_branch_match_prefix (input : ByteArray) (h : guardDiff remainingChecks input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock branchPrefixPath (accState input 1531 (accRest input)) =
      some (State.branchJumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have hz : UInt256.isZero (accRest input) = UInt256.ofNat 1 :=
    Logic.isZero_of_eq _ h
  simp [branchPrefixPath, State.branchJumpState, accState, hz, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc2,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_branch_mismatch (input : ByteArray) (h : guardDiff remainingChecks input ≠ 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock branchPath (accState input 1531 (accRest input)) =
      some (Main.trampolineState input 1536) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have hz : UInt256.isZero (accRest input) = UInt256.ofNat 0 :=
    Logic.isZero_of_ne _ h
  simp [branchPath, accState, hz, Logic.not_isTrue_zero, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc2,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_fallback_prefix (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock fallbackPrefixPath (Main.trampolineState input 1536) =
      some (State.fallbackJumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [fallbackPrefixPath, State.fallbackJumpState, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc2,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_fallback_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated fallbackJumpLocated (State.fallbackJumpState input) =
      some (Main.trampolineState input 1553) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 1553 = true :=
    Artifact.isValidJumpDest_index 1087 (by rfl)
  have hpc : (State.fallbackJumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1074 := by
    simp [State.fallbackJumpState, initialState, PCs.pc2, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jump fallbackJumpLocated rfl (State.fallbackJumpState input) 1553 [] hpc rfl (by simp) rfl (by norm_num) hjump).trans rfl

theorem run_return (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock returnPath (Main.trampolineState input 1540) =
      some (returnedState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [returnPath, returnedState, answerMemory, storeWord,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc2, PCs.pc3,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

end Challenge.Modexp.Submission.Proofs.Memo.V2.Trace
