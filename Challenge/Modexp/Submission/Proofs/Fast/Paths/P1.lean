import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 1 (instructions 1028..1038). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1028..1038, pc 1385..1399. -/
def blk1028 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1028 1 32,
   opAt 1029 (.Dup ⟨6, by decide⟩),
   opAt 1030 (.Dup ⟨2, by decide⟩),
   opAt 1031 .ADD,
   opAt 1032 .SUB,
   opAt 1033 .CALLDATALOAD,
   pushAt 1034 1 1,
   opAt 1035 .AND,
   opAt 1036 .ISZERO,
   pushAt 1037 2 1900,
   opAt 1038 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
