import Challenge.Ripemd160.Submission.H39Memo.A1000Advance
import Challenge.Ripemd160.Submission.H39Memo.A1000Single
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.H39Memo.A1000
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState

theorem run_advance_more (s : State) (n : Nat) (hn : n < 29)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode) :
    Stepper.runLocatedBlock advancePath (checked s n) = some (loop s (n + 1)) := by
  have hfit : 32 * (n + 2) < 2 ^ 256 := by omega
  have hv : (UInt256.ofNat (32 * (n + 2))).toNat = 32 * (n + 2) :=
    Logic.toNat_ofNat_self hfit
  have h992 : (992 : UInt256).toNat = 992 := by decide
  have hcond : UInt256.isTrue
      (UInt256.xor 992 (UInt256.ofNat (32 * (n + 2)))) := by
    unfold UInt256.isTrue
    intro hzero
    have hwordzero : UInt256.xor 992 (UInt256.ofNat (32 * (n + 2))) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      change (UInt256.xor 992 (UInt256.ofNat (32 * (n + 2)))).toNat = 0
      exact hzero
    have heq :=
      (Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic.wordXor_eq_zero_iff _ _).mp hwordzero
    have hnat := congrArg UInt256.toNat heq
    simp only [h992, hv] at hnat
    omega
  have hbranch := branch_true (opAt 1135 .JUMPI) s 3182 3161
    (UInt256.xor 992 (UInt256.ofNat (32 * (n + 2))))
    [UInt256.ofNat (32 * (n + 2)), cacheWord]
    rfl pc1135 (by decide) (by decide) (by simp) hcond hcode jump_loop
  change Stepper.runLocatedBlock (advancePrefix ++ [opAt 1135 .JUMPI])
    (checked s n) = some (loop s (n + 1))
  apply Stepper.runLocatedBlock_append _ _ _ _ _ (run_advancePrefix s n hrun) hrun
  rw [run_singleton]
  simpa only [loop, Nat.add_assoc, atPC,
    Challenge.EvmProof.Word.literal_eq_ofNat] using hbranch

theorem run_advance_last (s : State) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock advancePath (checked s 29) = some (tailEntry s) := by
  have hcond : ¬ UInt256.isTrue (UInt256.xor 992 992) := by decide
  have hbranch := branch_false (opAt 1135 .JUMPI) s 3182 3161
    (UInt256.xor 992 992) [992, cacheWord]
    rfl pc1135 (by decide) (by simp) hcond
  change Stepper.runLocatedBlock (advancePrefix ++ [opAt 1135 .JUMPI])
    (checked s 29) = some (tailEntry s)
  apply Stepper.runLocatedBlock_append _ _ _ _ _ (run_advancePrefix s 29 hrun) hrun
  rw [run_singleton]
  simpa only [tailEntry, atPC,
    Challenge.EvmProof.Word.literal_eq_ofNat] using hbranch

end Challenge.Ripemd160.Submission.H39Memo.A1000
