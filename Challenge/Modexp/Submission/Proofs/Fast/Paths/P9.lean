import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 9 (instructions 1469..1518). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1469..1518, pc 2141..2240. -/
def blk1469 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1469 .POP,
   opAt 1470 .POP,
   opAt 1471 (.Dup ⟨0, by decide⟩),
   pushAt 1472 2 8224,
   opAt 1473 .MLOAD,
   opAt 1474 .ADD,
   opAt 1475 (.Dup ⟨0, by decide⟩),
   pushAt 1476 2 8224,
   opAt 1477 .MSTORE,
   opAt 1478 .LT,
   pushAt 1479 2 8192,
   opAt 1480 .MSTORE,
   pushAt 1481 2 9440,
   opAt 1482 .MLOAD,
   opAt 1483 .MLOAD,
   pushAt 1484 2 9376,
   opAt 1485 .MLOAD,
   opAt 1486 .MUL,
   opAt 1487 (.Dup ⟨0, by decide⟩),
   pushAt 1488 2 9408,
   opAt 1489 .MLOAD,
   opAt 1490 .MLOAD,
   opAt 1491 (.Dup ⟨1, by decide⟩),
   opAt 1492 (.Dup ⟨1, by decide⟩),
   opAt 1493 .MUL,
   opAt 1494 (.Swap ⟨1, by decide⟩),
   pushAt 1495 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 1496 (.Swap ⟨1, by decide⟩),
   opAt 1497 .MULMOD,
   opAt 1498 (.Dup ⟨1, by decide⟩),
   opAt 1499 (.Dup ⟨1, by decide⟩),
   opAt 1500 .LT,
   opAt 1501 (.Dup ⟨2, by decide⟩),
   opAt 1502 .ADD,
   opAt 1503 (.Swap ⟨0, by decide⟩),
   opAt 1504 .SUB,
   opAt 1505 (.Swap ⟨0, by decide⟩),
   opAt 1506 .ISZERO,
   opAt 1507 .ISZERO,
   opAt 1508 .ADD,
   pushAt 1509 2 9440,
   opAt 1510 .MLOAD,
   pushAt 1511 1 32,
   opAt 1512 (.Swap ⟨0, by decide⟩),
   opAt 1513 .SUB,
   pushAt 1514 2 9408,
   opAt 1515 .MLOAD,
   pushAt 1516 1 32,
   opAt 1517 (.Swap ⟨0, by decide⟩),
   opAt 1518 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
