import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 6 (instructions 1314..1368). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1314..1319, pc 1841..1849. -/
def blk1314 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1314 .POP,
   opAt 1315 .POP,
   pushAt 1316 1 1,
   opAt 1317 .ADD,
   pushAt 1318 2 1769,
   opAt 1319 .JUMP]

/-- Instructions 1320..1332, pc 1850..1875. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1320 .JUMPDEST,
   opAt 1321 .POP,
   pushAt 1322 1 1,
   opAt 1323 (.Dup ⟨1, by decide⟩),
   pushAt 1324 2 3040,
   opAt 1325 .ADD,
   opAt 1326 .MSTORE,
   pushAt 1327 2 1876,
   pushAt 1328 2 1024,
   pushAt 1329 2 3072,
   pushAt 1330 2 1024,
   pushAt 1331 2 1939,
   opAt 1332 .JUMP]

/-- Instructions 1333..1340, pc 1876..1885. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1333 .JUMPDEST,
   opAt 1334 (.Dup ⟨4, by decide⟩),
   opAt 1335 (.Dup ⟨0, by decide⟩),
   opAt 1336 (.Dup ⟨2, by decide⟩),
   pushAt 1337 2 1024,
   opAt 1338 .ADD,
   opAt 1339 .SUB,
   opAt 1340 .RETURN]

/-- Instructions 1341..1344, pc 1886..1891. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1341 .JUMPDEST,
   opAt 1342 .POP,
   pushAt 1343 2 1196,
   opAt 1344 .JUMP]

/-- Instructions 1345..1350, pc 1892..1899. -/
def blk1345 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1345 .JUMPDEST,
   opAt 1346 .POP,
   opAt 1347 .POP,
   opAt 1348 .POP,
   pushAt 1349 2 1196,
   opAt 1350 .JUMP]

/-- Instructions 1351..1359, pc 1900..1910. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1351 .JUMPDEST,
   opAt 1352 .POP,
   opAt 1353 .POP,
   opAt 1354 .POP,
   opAt 1355 .POP,
   opAt 1356 .POP,
   opAt 1357 .POP,
   pushAt 1358 2 1196,
   opAt 1359 .JUMP]

/-- Instructions 1360..1361, pc 1911..1912. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1360 .JUMPDEST,
   pushAt 1361 2 256]

/-- Instructions 1362..1368, pc 1915..1925. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1362 .JUMPDEST,
   pushAt 1363 2 1926,
   opAt 1364 (.Dup ⟨2, by decide⟩),
   opAt 1365 (.Dup ⟨0, by decide⟩),
   opAt 1366 (.Dup ⟨0, by decide⟩),
   pushAt 1367 2 2467,
   opAt 1368 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
