import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 12 (instructions 1627..1682). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1627..1661, pc 2500..2634. -/
def blk1627 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1627 .JUMPDEST,
   opAt 1628 (.Dup ⟨1, by decide⟩),
   opAt 1629 .MLOAD,
   opAt 1630 (.Dup ⟨3, by decide⟩),
   opAt 1631 .MLOAD,
   opAt 1632 (.Dup ⟨1, by decide⟩),
   opAt 1633 .ADD,
   opAt 1634 (.Swap ⟨0, by decide⟩),
   opAt 1635 (.Dup ⟨1, by decide⟩),
   opAt 1636 .LT,
   opAt 1637 (.Swap ⟨0, by decide⟩),
   opAt 1638 (.Dup ⟨5, by decide⟩),
   opAt 1639 .ADD,
   opAt 1640 (.Swap ⟨4, by decide⟩),
   opAt 1641 (.Dup ⟨5, by decide⟩),
   opAt 1642 .LT,
   opAt 1643 .OR,
   opAt 1644 (.Swap ⟨3, by decide⟩),
   opAt 1645 (.Dup ⟨1, by decide⟩),
   opAt 1646 .MSTORE,
   pushAt 1647 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1648 .ADD,
   opAt 1649 (.Swap ⟨0, by decide⟩),
   pushAt 1650 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1651 .ADD,
   opAt 1652 (.Swap ⟨0, by decide⟩),
   opAt 1653 (.Swap ⟨1, by decide⟩),
   pushAt 1654 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1655 .ADD,
   opAt 1656 (.Swap ⟨1, by decide⟩),
   pushAt 1657 2 8224,
   opAt 1658 (.Dup ⟨1, by decide⟩),
   opAt 1659 .GT,
   pushAt 1660 2 2500,
   opAt 1661 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2641. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1662 .POP,
   opAt 1663 .POP,
   opAt 1664 .POP,
   pushAt 1665 2 8224,
   opAt 1666 .MSTORE]

/-- Instructions 1667..1682, pc 2642..2665. -/
def blk1667 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1667 .JUMPDEST,
   pushAt 1668 2 9440,
   opAt 1669 .MLOAD,
   pushAt 1670 2 9408,
   opAt 1671 .MLOAD,
   opAt 1672 (.Dup ⟨1, by decide⟩),
   pushAt 1673 2 7168,
   opAt 1674 .ADD,
   pushAt 1675 2 8256,
   opAt 1676 (.Swap ⟨0, by decide⟩),
   opAt 1677 .SUB,
   pushAt 1678 0 0,
   opAt 1679 (.Swap ⟨2, by decide⟩),
   opAt 1680 (.Swap ⟨0, by decide⟩),
   opAt 1681 (.Swap ⟨1, by decide⟩),
   opAt 1682 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
