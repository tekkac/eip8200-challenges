import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 13 (instructions 1683..1741). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1683..1723, pc 2666..2806. -/
def blk1683 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1683 .JUMPDEST,
   opAt 1684 (.Dup ⟨0, by decide⟩),
   opAt 1685 .MLOAD,
   opAt 1686 (.Dup ⟨2, by decide⟩),
   opAt 1687 .MLOAD,
   opAt 1688 (.Swap ⟨0, by decide⟩),
   opAt 1689 (.Dup ⟨1, by decide⟩),
   opAt 1690 (.Dup ⟨1, by decide⟩),
   opAt 1691 .LT,
   opAt 1692 (.Swap ⟨1, by decide⟩),
   opAt 1693 (.Swap ⟨0, by decide⟩),
   opAt 1694 .SUB,
   opAt 1695 (.Dup ⟨5, by decide⟩),
   opAt 1696 (.Dup ⟨1, by decide⟩),
   opAt 1697 .SUB,
   opAt 1698 (.Swap ⟨0, by decide⟩),
   opAt 1699 (.Dup ⟨6, by decide⟩),
   opAt 1700 (.Swap ⟨0, by decide⟩),
   opAt 1701 .LT,
   opAt 1702 (.Swap ⟨0, by decide⟩),
   opAt 1703 (.Swap ⟨1, by decide⟩),
   opAt 1704 .OR,
   opAt 1705 (.Swap ⟨4, by decide⟩),
   opAt 1706 .POP,
   opAt 1707 (.Dup ⟨3, by decide⟩),
   opAt 1708 .MSTORE,
   pushAt 1709 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1710 .ADD,
   opAt 1711 (.Swap ⟨0, by decide⟩),
   pushAt 1712 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1713 .ADD,
   opAt 1714 (.Swap ⟨0, by decide⟩),
   opAt 1715 (.Swap ⟨1, by decide⟩),
   pushAt 1716 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1717 .ADD,
   opAt 1718 (.Swap ⟨1, by decide⟩),
   pushAt 1719 2 8224,
   opAt 1720 (.Dup ⟨1, by decide⟩),
   opAt 1721 .GT,
   pushAt 1722 2 2666,
   opAt 1723 .JUMPI]

/-- Instructions 1724..1741, pc 2807..2862. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1724 .POP,
   opAt 1725 .POP,
   opAt 1726 .POP,
   opAt 1727 .ISZERO,
   pushAt 1728 2 8224,
   opAt 1729 .MLOAD,
   opAt 1730 .OR,
   pushAt 1731 32 115792089237316195423570985008687907853269984665640564039457584007913129638848,
   opAt 1732 .MUL,
   pushAt 1733 2 8256,
   opAt 1734 .ADD,
   pushAt 1735 2 9344,
   opAt 1736 .MLOAD,
   opAt 1737 (.Swap ⟨0, by decide⟩),
   opAt 1738 (.Dup ⟨2, by decide⟩),
   opAt 1739 .MCOPY,
   opAt 1740 .POP,
   opAt 1741 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
