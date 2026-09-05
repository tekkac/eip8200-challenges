import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 8 (instructions 1421..1468). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1421..1468, pc 1995..2140. -/
def blk1421 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1421 .JUMPDEST,
   opAt 1422 (.Dup ⟨3, by decide⟩),
   opAt 1423 (.Dup ⟨1, by decide⟩),
   opAt 1424 .MLOAD,
   opAt 1425 (.Dup ⟨1, by decide⟩),
   opAt 1426 (.Dup ⟨1, by decide⟩),
   opAt 1427 .MUL,
   opAt 1428 (.Swap ⟨1, by decide⟩),
   pushAt 1429 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 1430 (.Swap ⟨1, by decide⟩),
   opAt 1431 .MULMOD,
   opAt 1432 (.Dup ⟨1, by decide⟩),
   opAt 1433 (.Dup ⟨1, by decide⟩),
   opAt 1434 .LT,
   opAt 1435 (.Dup ⟨2, by decide⟩),
   opAt 1436 .ADD,
   opAt 1437 (.Swap ⟨0, by decide⟩),
   opAt 1438 .SUB,
   opAt 1439 (.Dup ⟨3, by decide⟩),
   opAt 1440 .MLOAD,
   opAt 1441 (.Swap ⟨1, by decide⟩),
   opAt 1442 (.Dup ⟨2, by decide⟩),
   opAt 1443 .ADD,
   opAt 1444 (.Swap ⟨1, by decide⟩),
   opAt 1445 (.Dup ⟨2, by decide⟩),
   opAt 1446 .LT,
   opAt 1447 .ADD,
   opAt 1448 (.Swap ⟨0, by decide⟩),
   opAt 1449 (.Dup ⟨4, by decide⟩),
   opAt 1450 .ADD,
   opAt 1451 (.Swap ⟨3, by decide⟩),
   opAt 1452 (.Dup ⟨4, by decide⟩),
   opAt 1453 .LT,
   opAt 1454 .ADD,
   opAt 1455 (.Swap ⟨2, by decide⟩),
   opAt 1456 (.Dup ⟨2, by decide⟩),
   opAt 1457 .MSTORE,
   pushAt 1458 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1459 .ADD,
   opAt 1460 (.Swap ⟨0, by decide⟩),
   pushAt 1461 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1462 .ADD,
   opAt 1463 (.Swap ⟨0, by decide⟩),
   opAt 1464 (.Dup ⟨5, by decide⟩),
   opAt 1465 (.Dup ⟨1, by decide⟩),
   opAt 1466 .GT,
   pushAt 1467 2 1995,
   opAt 1468 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
