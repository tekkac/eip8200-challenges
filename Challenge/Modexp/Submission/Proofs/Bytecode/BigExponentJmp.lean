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

theorem jump310 :
    Decode.isValidJumpDest submissionBytecode 310 = true :=
  Artifact.isValidJumpDest_index 265 (by rfl)



theorem jump58 :
    Decode.isValidJumpDest submissionBytecode 58 = true :=
  Artifact.isValidJumpDest_index 46 (by rfl)



theorem jump1039 :
    Decode.isValidJumpDest submissionBytecode 1039 = true :=
  Artifact.isValidJumpDest_index 777 (by rfl)


theorem jump1090 :
    Decode.isValidJumpDest submissionBytecode 1090 = true :=
  Artifact.isValidJumpDest_index 816 (by rfl)


theorem jump963 :
    Decode.isValidJumpDest submissionBytecode 963 = true :=
  Artifact.isValidJumpDest_index 734 (by rfl)



theorem jump1104 :
    Decode.isValidJumpDest submissionBytecode 1104 = true :=
  Artifact.isValidJumpDest_index 827 (by rfl)


theorem jump946 :
    Decode.isValidJumpDest submissionBytecode 946 = true :=
  Artifact.isValidJumpDest_index 719 (by rfl)
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
