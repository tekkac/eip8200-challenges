import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 10 (instructions 1519..1568). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1519..1568, pc 2241..2391. -/
def blk1519 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1519 .JUMPDEST,
   opAt 1520 (.Dup ⟨3, by decide⟩),
   opAt 1521 (.Dup ⟨1, by decide⟩),
   opAt 1522 .MLOAD,
   opAt 1523 (.Dup ⟨1, by decide⟩),
   opAt 1524 (.Dup ⟨1, by decide⟩),
   opAt 1525 .MUL,
   opAt 1526 (.Swap ⟨1, by decide⟩),
   pushAt 1527 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 1528 (.Swap ⟨1, by decide⟩),
   opAt 1529 .MULMOD,
   opAt 1530 (.Dup ⟨1, by decide⟩),
   opAt 1531 (.Dup ⟨1, by decide⟩),
   opAt 1532 .LT,
   opAt 1533 (.Dup ⟨2, by decide⟩),
   opAt 1534 .ADD,
   opAt 1535 (.Swap ⟨0, by decide⟩),
   opAt 1536 .SUB,
   opAt 1537 (.Dup ⟨3, by decide⟩),
   opAt 1538 .MLOAD,
   opAt 1539 (.Swap ⟨1, by decide⟩),
   opAt 1540 (.Dup ⟨2, by decide⟩),
   opAt 1541 .ADD,
   opAt 1542 (.Swap ⟨1, by decide⟩),
   opAt 1543 (.Dup ⟨2, by decide⟩),
   opAt 1544 .LT,
   opAt 1545 .ADD,
   opAt 1546 (.Swap ⟨0, by decide⟩),
   opAt 1547 (.Dup ⟨4, by decide⟩),
   opAt 1548 .ADD,
   opAt 1549 (.Swap ⟨3, by decide⟩),
   opAt 1550 (.Dup ⟨4, by decide⟩),
   opAt 1551 .LT,
   opAt 1552 .ADD,
   opAt 1553 (.Swap ⟨2, by decide⟩),
   opAt 1554 (.Dup ⟨2, by decide⟩),
   pushAt 1555 1 32,
   opAt 1556 .ADD,
   opAt 1557 .MSTORE,
   pushAt 1558 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1559 .ADD,
   opAt 1560 (.Swap ⟨0, by decide⟩),
   pushAt 1561 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1562 .ADD,
   opAt 1563 (.Swap ⟨0, by decide⟩),
   pushAt 1564 2 8224,
   opAt 1565 (.Dup ⟨2, by decide⟩),
   opAt 1566 .GT,
   pushAt 1567 2 2241,
   opAt 1568 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
