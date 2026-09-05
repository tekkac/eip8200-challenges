import Challenge.Ripemd160.Submission.H39Memo.Artifact
import Challenge.Ripemd160.Submission.H39Memo.A1000State

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo.A1000
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

abbrev Located := Stepper.Located Artifact.h39Artifact .Osaka

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.h39Instructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) : Located :=
  ⟨index, .op op, hget, ⟨hopcode, hplain, havailable⟩⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.h39Instructions[index]? = some (.push width value) := by rfl)
    (hwf : Stepper.WellFormed .Osaka (.push width value) := by decide) : Located :=
  ⟨index, .push width value, hget, hwf⟩

def firstPrefix : List Located :=
  [opAt 1110 (.JUMPDEST),
   pushAt 1111 32 cacheWord,
   pushAt 1112 0 0,
   opAt 1113 (.CALLDATALOAD),
   opAt 1114 (.Dup ⟨1, by decide⟩),
   opAt 1115 (.XOR),
   pushAt 1116 2 3258]

def firstPath : List Located :=
  [opAt 1110 (.JUMPDEST),
   pushAt 1111 32 cacheWord,
   pushAt 1112 0 0,
   opAt 1113 (.CALLDATALOAD),
   opAt 1114 (.Dup ⟨1, by decide⟩),
   opAt 1115 (.XOR),
   pushAt 1116 2 3258,
   opAt 1117 (.JUMPI)]

def cachePath : List Located :=
  [opAt 1118 (.Swap ⟨0, by decide⟩),
   opAt 1119 (.POP),
   pushAt 1120 1 32]

def loopPrefix : List Located :=
  [opAt 1121 (.JUMPDEST),
   opAt 1122 (.Dup ⟨0, by decide⟩),
   opAt 1123 (.CALLDATALOAD),
   opAt 1124 (.Dup ⟨2, by decide⟩),
   opAt 1125 (.XOR),
   pushAt 1126 2 3251]

def checkPath : List Located :=
  [opAt 1121 (.JUMPDEST),
   opAt 1122 (.Dup ⟨0, by decide⟩),
   opAt 1123 (.CALLDATALOAD),
   opAt 1124 (.Dup ⟨2, by decide⟩),
   opAt 1125 (.XOR),
   pushAt 1126 2 3251,
   opAt 1127 (.JUMPI)]

def advancePrefix : List Located :=
  [pushAt 1128 1 32,
   opAt 1129 (.ADD),
   opAt 1130 (.Dup ⟨0, by decide⟩),
   pushAt 1131 2 992,
   opAt 1132 (.XOR),
   opAt 1133 (.JUMPDEST),
   pushAt 1134 2 3161]

def advancePath : List Located :=
  [pushAt 1128 1 32,
   opAt 1129 (.ADD),
   opAt 1130 (.Dup ⟨0, by decide⟩),
   pushAt 1131 2 992,
   opAt 1132 (.XOR),
   opAt 1133 (.JUMPDEST),
   pushAt 1134 2 3161,
   opAt 1135 (.JUMPI)]

def tailPrefix : List Located :=
  [opAt 1136 (.Swap ⟨0, by decide⟩),
   opAt 1137 (.POP),
   opAt 1138 (.CALLDATALOAD),
   pushAt 1139 32 tailWord,
   opAt 1140 (.XOR),
   pushAt 1141 2 1006]

def tailPath : List Located :=
  [opAt 1136 (.Swap ⟨0, by decide⟩),
   opAt 1137 (.POP),
   opAt 1138 (.CALLDATALOAD),
   pushAt 1139 32 tailWord,
   opAt 1140 (.XOR),
   pushAt 1141 2 1006,
   opAt 1142 (.JUMPI)]

def answerPath : List Located :=
  [pushAt 1143 20 972889429405991776604892044862621566948497025487,
   pushAt 1144 0 0,
   opAt 1145 (.MSTORE),
   pushAt 1146 1 32,
   pushAt 1147 0 0,
   opAt 1148 (.RETURN)]

def failPath : List Located :=
  [opAt 1149 (.JUMPDEST),
   opAt 1150 (.POP),
   opAt 1151 (.POP),
   pushAt 1152 2 1006,
   opAt 1153 (.JUMP)]

def notAPath : List Located :=
  [opAt 1154 (.JUMPDEST),
   opAt 1155 (.POP),
   pushAt 1156 2 1696,
   opAt 1157 (.JUMP)]

end Challenge.Ripemd160.Submission.H39Memo.A1000
