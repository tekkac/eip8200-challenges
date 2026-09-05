import Challenge.Modexp.Submission.Proofs.Memo.PCs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.V2.Paths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Memo

def earlyPrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1051 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 1052 1 32,
   Main.opAt 1053 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 1054 2 1553
  ]

def earlyJumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1055 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

def checksPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 1056 1 1,
   Main.pushAt 1057 0 0,
   Main.opAt 1058 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1059 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.pushAt 1060 1 1,
   Main.pushAt 1061 1 64,
   Main.opAt 1062 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1063 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1064 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 1065 32 19168523805780691591649194585559922978212372797203590076661305677823631949824,
   Main.pushAt 1066 1 96,
   Main.opAt 1067 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1068 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1069 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def branchPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1070 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.ISZERO)),
   Main.pushAt 1071 2 1540,
   Main.opAt 1072 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))
  ]

def branchPrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1070 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.ISZERO)),
   Main.pushAt 1071 2 1540
  ]

def branchJumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1072 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

def fallbackPrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 1073 2 1553
  ]

def fallbackJumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1074 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMP))

def returnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1075 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 1076 0 0,
   Main.opAt 1077 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.ISZERO)),
   Main.pushAt 1078 0 0,
   Main.opAt 1079 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 1080 0 0,
   Main.opAt 1081 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.ISZERO)),
   Main.pushAt 1082 1 31,
   Main.opAt 1083 (EvmSemantics.Operation.System (EvmSemantics.Operation.SystemOps.RETURN))
  ]

end Challenge.Modexp.Submission.Proofs.Memo.V2.Paths
