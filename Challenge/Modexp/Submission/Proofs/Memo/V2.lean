import Challenge.Modexp.Submission.Proofs.Memo.V2.Trace
import Challenge.Modexp.Submission.Proofs.Memo.V2.Spec

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.V2

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Memo
open Logic Dispatch State Paths Trace

private def sound {s t : State} (path : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka))
    (hrun : s.halt = .Running)
    (h : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

private def soundOne {s t : State}
    {located : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka}
    (hrun : s.halt = .Running)
    (h : Challenge.EvmProof.Stepper.runLocated located s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocated_sound hcode hfork h hrun hnp

def gasSteps_match (input : ByteArray) (h : guardDiff Data.checks input = 0) :
    Challenge.EvmProof.GasSteps (Main.trampolineState input 1473) (returnedState input) := by
  have ⟨h32, hrest⟩ := (guardDiff_split input).1 h
  exact ((((((sound earlyPrefixPath rfl (run_early_prefix input) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_early_jump_not_taken input h32) rfl rfl deployAddress_not_precompile)).trans
    (sound checksPath rfl (run_checks input) rfl rfl deployAddress_not_precompile)).trans
    (sound branchPrefixPath rfl (run_branch_match_prefix input hrest) rfl rfl deployAddress_not_precompile)).trans
    (soundOne rfl (run_branch_jump input) rfl rfl deployAddress_not_precompile)).trans
    (sound returnPath rfl (run_return input) rfl rfl deployAddress_not_precompile))

def gasSteps_fallback (input : ByteArray) (h : guardDiff Data.checks input ≠ 0) :
    Challenge.EvmProof.GasSteps (Main.trampolineState input 1473) (Main.trampolineState input 1553) := by
  by_cases h32 : MachineState.readWord input 32 = 0
  · have hrest : guardDiff remainingChecks input ≠ 0 := by
      intro hr
      apply h
      rw [guardDiff_split]
      exact ⟨h32, hr⟩
    exact (((((sound earlyPrefixPath rfl (run_early_prefix input) rfl rfl deployAddress_not_precompile).trans
      (soundOne rfl (run_early_jump_not_taken input h32) rfl rfl deployAddress_not_precompile)).trans
      (sound checksPath rfl (run_checks input) rfl rfl deployAddress_not_precompile)).trans
      (sound branchPath rfl (run_branch_mismatch input hrest) rfl rfl deployAddress_not_precompile)).trans
      (sound fallbackPrefixPath rfl (run_fallback_prefix input) rfl rfl deployAddress_not_precompile)).trans
      (soundOne rfl (run_fallback_jump input) rfl rfl deployAddress_not_precompile)
  · exact ((sound earlyPrefixPath rfl (run_early_prefix input) rfl rfl deployAddress_not_precompile).trans
      (soundOne rfl (run_early_jump_taken input h32) rfl rfl deployAddress_not_precompile))

@[simp] theorem returnedState_isDone (input : ByteArray) :
    (returnedState input).isDone = true := by
  simp [returnedState, State.isDone, State.isHalted, State.isRunning]
  rfl

theorem returnedState_result (input : ByteArray) (h : guardDiff Data.checks input = 0) :
    (returnedState input).toResult = .returned (spec input) := by
  have hm : WordsMatch Data.checks input := (guardDiff_eq_zero_iff _ _).1 h
  rw [State.toResult_returned _ (by rfl)]
  change ExecutionResult.returned (MachineState.readPadded answerMemory 31 1) = _
  rw [answerMemory_read, Spec.spec_eq hm]

end Challenge.Modexp.Submission.Proofs.Memo.V2
