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

@[simp] theorem selectPCs (i : Nat) (hi : 777 ≤ i)
    (hii : i ≤ 826) :
    Artifact.submissionArtifact.instructionPC i =
      ([1039,1040,1041,1042,1043,1044,1047,1048,1049,1051,1052,1053,
        1056,1057,1058,1059,1062,1063,1064,1065,1066,1067,1068,1069,
        1070,1071,1072,1075,1076,1077,1078,1079,1080,1082,1083,1084,
        1085,1086,1089,1090,1091,1092,1093,1094,1096,1097,1098,1099,
        1100,1103])[i - 777]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
