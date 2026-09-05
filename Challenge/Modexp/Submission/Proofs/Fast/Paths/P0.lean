import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 0 (instructions 977..1027). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 977..985, pc 1314..1326. -/
def blk977 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 977 .JUMPDEST,
   pushAt 978 1 64,
   opAt 979 .CALLDATALOAD,
   opAt 980 (.Dup ⟨0, by decide⟩),
   pushAt 981 1 33,
   opAt 982 .GT,
   opAt 983 .JUMPDEST,
   pushAt 984 2 1886,
   opAt 985 .JUMPI]

/-- Instructions 986..1002, pc 1327..1352. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 986 1 32,
   opAt 987 .CALLDATALOAD,
   pushAt 988 0 0,
   opAt 989 .CALLDATALOAD,
   opAt 990 (.Dup ⟨2, by decide⟩),
   pushAt 991 2 1024,
   opAt 992 .LT,
   opAt 993 (.Dup ⟨2, by decide⟩),
   pushAt 994 2 1024,
   opAt 995 .LT,
   opAt 996 .OR,
   opAt 997 (.Dup ⟨1, by decide⟩),
   pushAt 998 2 1024,
   opAt 999 .LT,
   opAt 1000 .OR,
   pushAt 1001 2 1892,
   opAt 1002 .JUMPI]

/-- Instructions 1003..1027, pc 1353..1384. -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1003 (.Dup ⟨2, by decide⟩),
   pushAt 1004 1 31,
   opAt 1005 .ADD,
   pushAt 1006 1 5,
   opAt 1007 .SHR,
   opAt 1008 (.Dup ⟨0, by decide⟩),
   pushAt 1009 1 5,
   opAt 1010 .SHL,
   opAt 1011 (.Dup ⟨3, by decide⟩),
   opAt 1012 (.Dup ⟨3, by decide⟩),
   opAt 1013 .ADD,
   pushAt 1014 1 96,
   opAt 1015 .ADD,
   opAt 1016 (.Dup ⟨5, by decide⟩),
   opAt 1017 (.Dup ⟨2, by decide⟩),
   opAt 1018 .SUB,
   pushAt 1019 1 3,
   opAt 1020 .SHL,
   opAt 1021 (.Dup ⟨1, by decide⟩),
   opAt 1022 .CALLDATALOAD,
   opAt 1023 (.Swap ⟨0, by decide⟩),
   opAt 1024 .SHR,
   opAt 1025 .ISZERO,
   pushAt 1026 2 1900,
   opAt 1027 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
