import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 7 (instructions 1369..1420). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1369..1375, pc 1926..1935. -/
def blk1369 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1369 .JUMPDEST,
   pushAt 1370 1 1,
   opAt 1371 (.Swap ⟨0, by decide⟩),
   opAt 1372 .SUB,
   opAt 1373 (.Dup ⟨0, by decide⟩),
   pushAt 1374 2 1915,
   opAt 1375 .JUMPI]

/-- Instructions 1376..1378, pc 1936..1938. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1376 .POP,
   opAt 1377 .POP,
   opAt 1378 .JUMP]

/-- Instructions 1379..1405, pc 1939..1973. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1379 .JUMPDEST,
   pushAt 1380 2 9344,
   opAt 1381 .MLOAD,
   opAt 1382 (.Dup ⟨0, by decide⟩),
   pushAt 1383 1 64,
   opAt 1384 .ADD,
   opAt 1385 .CALLDATASIZE,
   pushAt 1386 2 8192,
   opAt 1387 .CALLDATACOPY,
   opAt 1388 (.Dup ⟨0, by decide⟩),
   opAt 1389 (.Dup ⟨3, by decide⟩),
   opAt 1390 .ADD,
   pushAt 1391 1 32,
   opAt 1392 (.Swap ⟨0, by decide⟩),
   opAt 1393 .SUB,
   pushAt 1394 1 32,
   opAt 1395 (.Dup ⟨4, by decide⟩),
   opAt 1396 .SUB,
   opAt 1397 (.Swap ⟨3, by decide⟩),
   opAt 1398 .POP,
   opAt 1399 (.Swap ⟨0, by decide⟩),
   opAt 1400 .POP,
   pushAt 1401 1 32,
   opAt 1402 (.Dup ⟨2, by decide⟩),
   opAt 1403 .SUB,
   opAt 1404 (.Swap ⟨1, by decide⟩),
   opAt 1405 .POP]

/-- Instructions 1406..1420, pc 1974..1994. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1406 .JUMPDEST,
   opAt 1407 (.Dup ⟨0, by decide⟩),
   opAt 1408 .MLOAD,
   pushAt 1409 0 0,
   pushAt 1410 2 9440,
   opAt 1411 .MLOAD,
   opAt 1412 (.Dup ⟨4, by decide⟩),
   pushAt 1413 1 32,
   opAt 1414 .ADD,
   pushAt 1415 2 9344,
   opAt 1416 .MLOAD,
   opAt 1417 .ADD,
   pushAt 1418 1 32,
   opAt 1419 (.Swap ⟨0, by decide⟩),
   opAt 1420 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
