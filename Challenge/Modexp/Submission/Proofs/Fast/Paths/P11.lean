import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 11 (instructions 1569..1626). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1569..1594, pc 2392..2459. -/
def blk1569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1569 .POP,
   opAt 1570 .POP,
   opAt 1571 (.Swap ⟨0, by decide⟩),
   opAt 1572 .POP,
   opAt 1573 (.Swap ⟨0, by decide⟩),
   opAt 1574 .POP,
   opAt 1575 (.Dup ⟨0, by decide⟩),
   pushAt 1576 2 8224,
   opAt 1577 .MLOAD,
   opAt 1578 .ADD,
   opAt 1579 (.Dup ⟨0, by decide⟩),
   pushAt 1580 2 8256,
   opAt 1581 .MSTORE,
   opAt 1582 .LT,
   pushAt 1583 2 8192,
   opAt 1584 .MLOAD,
   opAt 1585 .ADD,
   pushAt 1586 2 8224,
   opAt 1587 .MSTORE,
   pushAt 1588 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1589 .ADD,
   opAt 1590 (.Dup ⟨2, by decide⟩),
   opAt 1591 (.Dup ⟨1, by decide⟩),
   opAt 1592 .GT,
   pushAt 1593 2 1974,
   opAt 1594 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2466. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1595 .POP,
   opAt 1596 .POP,
   opAt 1597 .POP,
   pushAt 1598 2 2642,
   opAt 1599 .JUMP]

/-- Instructions 1600..1626, pc 2467..2499. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1600 .JUMPDEST,
   pushAt 1601 2 9344,
   opAt 1602 .MLOAD,
   opAt 1603 (.Dup ⟨0, by decide⟩),
   opAt 1604 (.Dup ⟨2, by decide⟩),
   opAt 1605 .ADD,
   pushAt 1606 1 32,
   opAt 1607 (.Swap ⟨0, by decide⟩),
   opAt 1608 .SUB,
   opAt 1609 (.Dup ⟨1, by decide⟩),
   opAt 1610 (.Dup ⟨4, by decide⟩),
   opAt 1611 .ADD,
   pushAt 1612 1 32,
   opAt 1613 (.Swap ⟨0, by decide⟩),
   opAt 1614 .SUB,
   opAt 1615 (.Swap ⟨2, by decide⟩),
   opAt 1616 .POP,
   opAt 1617 (.Swap ⟨2, by decide⟩),
   opAt 1618 .POP,
   opAt 1619 .POP,
   pushAt 1620 2 9440,
   opAt 1621 .MLOAD,
   pushAt 1622 0 0,
   opAt 1623 (.Swap ⟨0, by decide⟩),
   opAt 1624 (.Swap ⟨0, by decide⟩),
   opAt 1625 (.Swap ⟨2, by decide⟩),
   opAt 1626 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
