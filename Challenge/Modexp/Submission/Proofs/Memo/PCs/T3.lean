import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc3 (i : Nat) (hlo : 1082 ≤ i) (hhi : i ≤ 1116) :
    Artifact.submissionArtifact.instructionPC i =
      [1547,1549,1550,1551,1552,1553,1554,1556,1557,1558,1559,1561,1563,1564,1565,1566,1567,1569,1570,1571,1572,1605,1607,1608,1609,1610,1611,1614,1615,1618,1619,1620,1621,1622,1623][i - 1082]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
