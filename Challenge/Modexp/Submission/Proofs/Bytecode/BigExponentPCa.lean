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

@[simp] theorem exponentPCs (i : Nat) (hi : 717 ≤ i) (hii : i ≤ 755) :
    Artifact.submissionArtifact.instructionPC i =
      ([944,945,946,947,948,949,950,951,954,955,956,957,958,959,960,961,
        962,963,964,966,967,968,969,972,973,975,976,977,979,980,981,982,
        985,986,987,990,993,996,999])[i - 717]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
