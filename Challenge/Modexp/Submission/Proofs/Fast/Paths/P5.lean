import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 5 (instructions 1255..1313). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1255..1263, pc 1736..1754. -/
def blk1255 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1255 .JUMPDEST,
   opAt 1256 .POP,
   opAt 1257 .POP,
   pushAt 1258 2 1755,
   pushAt 1259 2 2048,
   pushAt 1260 2 6144,
   pushAt 1261 2 1024,
   pushAt 1262 2 1939,
   opAt 1263 .JUMP]

/-- Instructions 1264..1264, pc 1755..1755. -/
def blk1264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1264 .JUMPDEST]

/-- Instructions 1265..1271, pc 1756..1768. -/
def blk1265 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1265 .JUMPDEST,
   pushAt 1266 2 9344,
   opAt 1267 .MLOAD,
   pushAt 1268 2 4096,
   pushAt 1269 2 1024,
   opAt 1270 .MCOPY,
   pushAt 1271 0 0]

/-- Instructions 1272..1278, pc 1769..1777. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1272 .JUMPDEST,
   opAt 1273 (.Dup ⟨4, by decide⟩),
   opAt 1274 (.Dup ⟨1, by decide⟩),
   opAt 1275 .LT,
   opAt 1276 .ISZERO,
   pushAt 1277 2 1850,
   opAt 1278 .JUMPI]

/-- Instructions 1279..1286, pc 1778..1787. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1279 2 2922,
   opAt 1280 .JUMP]

/-- Instructions 1287..1293, pc 1789..1805. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1287 .JUMPDEST,
   pushAt 1288 2 1806,
   pushAt 1289 2 1024,
   pushAt 1290 2 1024,
   pushAt 1291 2 1024,
   pushAt 1292 2 1939,
   opAt 1293 .JUMP]

/-- Instructions 1294..1300, pc 1806..1814. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1294 .JUMPDEST,
   opAt 1295 (.Dup ⟨1, by decide⟩),
   opAt 1296 (.Dup ⟨1, by decide⟩),
   opAt 1297 .AND,
   opAt 1298 .ISZERO,
   pushAt 1299 2 1832,
   opAt 1300 .JUMPI]

/-- Instructions 1301..1306, pc 1815..1830. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1301 2 1831,
   pushAt 1302 2 1024,
   pushAt 1303 2 2048,
   pushAt 1304 2 1024,
   pushAt 1305 2 1939,
   opAt 1306 .JUMP]

/-- Instructions 1307..1307, pc 1831..1831. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1307 .JUMPDEST]

/-- Instructions 1308..1313, pc 1832..1840. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1308 .JUMPDEST,
   pushAt 1309 1 1,
   opAt 1310 .SHR,
   opAt 1311 (.Dup ⟨0, by decide⟩),
   pushAt 1312 2 1789,
   opAt 1313 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
