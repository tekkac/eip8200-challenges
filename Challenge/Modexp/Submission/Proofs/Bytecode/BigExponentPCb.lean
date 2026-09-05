import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! # Program-counter tables for the multi-limb exponentiation path

Kept in a module with minimal imports: `interval_cases … <;> decide` over these
ranges is elaborated far more cheaply without the whole `Big*` simp environment
in scope.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp

@[simp] theorem exponentMidPCs (i : Nat) (hi : 756 ≤ i)
    (hii : i ≤ 776) :
    Artifact.submissionArtifact.instructionPC i =
      ([1000,1001,1004,1005,1008,1011,1014,1015,1016,1019,1020,1021,
        1024,1027,1030,1033,1034,1035,1036,1037,1038])[i - 756]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
