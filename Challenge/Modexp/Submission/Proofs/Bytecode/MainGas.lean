import Challenge.Modexp.Submission.Proofs.Bytecode.MainTrampolinesLow
import Challenge.Modexp.Submission.Proofs.Bytecode.MainTrampolinesHigh
import Challenge.Modexp.Submission.Proofs.Bytecode.MainHeaderLoad
import Challenge.Modexp.Submission.Proofs.Bytecode.MainHeaderCheck
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

private def gasSteps_tramp0 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (trampolineState input 1314) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tramp0Path rfl rfl (run_tramp0 input)
      rfl deployAddress_not_precompile

/-- The body's own `JUMPDEST`, reached directly by the retargeted entry push. -/
private def gasSteps_tramp7Dest (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 1196)
      (headerEntryState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tramp7DestPath rfl rfl
      (run_tramp7Dest input) rfl deployAddress_not_precompile

private def gasSteps_tramp1 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 14)
      (trampolineState input 53) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tramp1Path rfl rfl (run_tramp1 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp2 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 53)
      (trampolineState input 99) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tramp2Path rfl rfl (run_tramp2 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp3 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 99)
      (trampolineState input 305) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tramp3Path rfl rfl (run_tramp3 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp4 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 305)
      (trampolineState input 434) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tramp4Path rfl rfl (run_tramp4 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp5 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 434)
      (trampolineState input 512) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tramp5Path rfl rfl (run_tramp5 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp6 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 512)
      (trampolineState input 699) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tramp6Path rfl rfl (run_tramp6 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp7 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 699)
      (headerEntryState input) := by
  apply Challenge.EvmProof.GasSteps.trans
  · exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka tramp7JumpPath rfl rfl
        (run_tramp7Jump input) rfl deployAddress_not_precompile
  · exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka tramp7DestPath rfl rfl
        (run_tramp7Dest input) rfl deployAddress_not_precompile

private def gasSteps_headerLoad (input : ByteArray) :
    Challenge.EvmProof.GasSteps (headerEntryState input)
      (headerLoadedState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka headerLoadPath rfl rfl (run_headerLoad input)
      rfl deployAddress_not_precompile

private def gasSteps_headerCheck (input : ByteArray) :
    Challenge.EvmProof.GasSteps (headerLoadedState input) (headerState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka headerCheckPath rfl rfl
      (run_headerCheck input) rfl deployAddress_not_precompile

@[simp] private theorem gasSteps_tramp0_cost (input : ByteArray) :
    (gasSteps_tramp0 input).cost = 11 := by rfl

@[simp] private theorem gasSteps_tramp7Dest_cost (input : ByteArray) :
    (gasSteps_tramp7Dest input).cost = 1 := by rfl

@[simp] private theorem gasSteps_tramp1_cost (input : ByteArray) :
    (gasSteps_tramp1 input).cost = 12 := by rfl

@[simp] private theorem gasSteps_tramp2_cost (input : ByteArray) :
    (gasSteps_tramp2 input).cost = 12 := by rfl

@[simp] private theorem gasSteps_tramp3_cost (input : ByteArray) :
    (gasSteps_tramp3 input).cost = 12 := by rfl

@[simp] private theorem gasSteps_tramp4_cost (input : ByteArray) :
    (gasSteps_tramp4 input).cost = 12 := by rfl

@[simp] private theorem gasSteps_tramp5_cost (input : ByteArray) :
    (gasSteps_tramp5 input).cost = 12 := by rfl

@[simp] private theorem gasSteps_tramp6_cost (input : ByteArray) :
    (gasSteps_tramp6 input).cost = 12 := by rfl

@[simp] private theorem gasSteps_tramp7_cost (input : ByteArray) :
    (gasSteps_tramp7 input).cost = 13 := by rfl

@[simp] private theorem gasSteps_headerLoad_cost (input : ByteArray) :
    (gasSteps_headerLoad input).cost = 17 := by rfl

@[simp] private theorem gasSteps_headerCheck_cost (input : ByteArray) :
    (gasSteps_headerCheck input).cost = 11 := by rfl

/-- The header block starting from the body `JUMPDEST` at pc 1196 rather than
from the entry.  The appended fast path reaches that pc itself, so the entry hop
is factored out. -/
def gasSteps_headerFromBody (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 1196)
      (headerState input) := by
  exact (gasSteps_tramp7Dest input).trans <|
    (gasSteps_headerLoad input).trans (gasSteps_headerCheck input)

/-- Entry hop into the appended fast path. -/
def gasSteps_entryHop (input : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (trampolineState input 1314) := gasSteps_tramp0 input

/-- The reference header block, prefixed by whatever trace reaches the body
`JUMPDEST` at pc 1196.  The appended fast path supplies that prefix on the
inputs it declines. -/
def gasSteps_header (input : ByteArray) (_hvalid : ValidInput input)
    (entry : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (trampolineState input 1196)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (headerState input) :=
  entry.trans (gasSteps_headerFromBody input)

end Challenge.Modexp.Submission.Proofs.Bytecode.Main
