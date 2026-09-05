import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 15 (instructions 1768..1780).

`R1B` (pc 2901) sits in front of the first `DOUBLE256` call.  When the
modulus's most significant bit is set, `radix ^ n < 2 * m`, so `R mod m` is
just `radix ^ n - m` — one borrow-propagating subtraction.  `CSUB` already
computes `t[n] * radix ^ n + t_low - m` selected against `m`, so storing
`t[n] := 1` over the still-zero `t` block and entering `CSUB` with `pd = R1`
produces `R mod m` in a single pass over the limbs instead of the 256 modular
doublings `DOUBLE256` performs.  Every other modulus falls through to
`DOUBLE256` unchanged.

The two basic blocks are

* `blk1768` (idx 1768..1775, pc 2901..2911) — `JUMPDEST`, the top-bit test
  `MLOAD 0; PUSH1 255; SHR; ISZERO` and the `JUMPI` back to `DOUBLE256`;
* `blk1776` (idx 1776..1780, pc 2912..2921) — `MSTORE TN 1` and the tail call
  into `CSUB` (pc 2642).

Both leave the incoming stack `[px, ret]` exactly as `DOUBLE256` and `CSUB`
expect it, so neither call site moves. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1768..1775, pc 2901..2911: the top-bit test and the branch
back into `DOUBLE256`. -/
def blk1768 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1768 .JUMPDEST,
   pushAt 1769 0 0,
   opAt 1770 .MLOAD,
   pushAt 1771 1 255,
   opAt 1772 .SHR,
   opAt 1773 .ISZERO,
   pushAt 1774 2 1911,
   opAt 1775 .JUMPI]

/-- Instructions 1776..1780, pc 2912..2921: `t[n] := 1` and the tail call into
`CSUB`. -/
def blk1776 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1776 1 1,
   pushAt 1777 2 8224,
   opAt 1778 .MSTORE,
   pushAt 1779 2 2642,
   opAt 1780 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
