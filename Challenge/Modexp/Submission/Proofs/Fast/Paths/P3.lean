import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 3 (instructions 1138..1194). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1138..1147, pc 1533..1554. -/
def blk1138 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1138 .JUMPDEST,
   pushAt 1139 2 9344,
   opAt 1140 .MLOAD,
   pushAt 1141 2 4096,
   pushAt 1142 2 5120,
   opAt 1143 .MCOPY,
   pushAt 1144 2 1555,
   pushAt 1145 2 5120,
   pushAt 1146 2 2863,
   opAt 1147 .JUMP]

/-- Instructions 1148..1154, pc 1555..1567. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1148 .JUMPDEST,
   pushAt 1149 2 9344,
   opAt 1150 .MLOAD,
   pushAt 1151 2 4096,
   pushAt 1152 2 6144,
   opAt 1153 .MCOPY,
   pushAt 1154 1 5]

/-- Instructions 1155..1161, pc 1569..1585. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1155 .JUMPDEST,
   pushAt 1156 2 1586,
   pushAt 1157 2 6144,
   pushAt 1158 2 6144,
   pushAt 1159 2 6144,
   pushAt 1160 2 1939,
   opAt 1161 .JUMP]

/-- Instructions 1162..1173, pc 1586..1604. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1162 .JUMPDEST,
   opAt 1163 (.Dup ⟨2, by decide⟩),
   opAt 1164 (.Dup ⟨1, by decide⟩),
   opAt 1165 .SHR,
   pushAt 1166 1 1,
   opAt 1167 .AND,
   pushAt 1168 2 1024,
   opAt 1169 .MUL,
   pushAt 1170 2 4096,
   opAt 1171 .ADD,
   pushAt 1172 2 2971,
   opAt 1173 .JUMP]

/-- Instructions 1178..1183, pc 1615..1622. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1178 .JUMPDEST,
   opAt 1179 .POP,
   opAt 1180 (.Dup ⟨0, by decide⟩),
   opAt 1181 .ISZERO,
   pushAt 1182 2 1631,
   opAt 1183 .JUMPI]

/-- Instructions 1184..1188, pc 1623..1630. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1184 1 1,
   opAt 1185 (.Swap ⟨0, by decide⟩),
   opAt 1186 .SUB,
   pushAt 1187 2 1569,
   opAt 1188 .JUMP]

/-- Instructions 1189..1194, pc 1631..1638. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1189 .JUMPDEST,
   opAt 1190 .POP,
   opAt 1191 (.Dup ⟨2, by decide⟩),
   opAt 1192 .ISZERO,
   pushAt 1193 2 1756,
   opAt 1194 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
