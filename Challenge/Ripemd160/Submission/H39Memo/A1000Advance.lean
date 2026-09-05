import Challenge.Ripemd160.Submission.H39Memo.A1000Prefix

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.A1000
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState

theorem run_advancePrefix (s : State) (n : Nat) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock advancePrefix (checked s n) =
      some (atPC s 3182 [3161,
        UInt256.xor 992 (UInt256.ofNat (32 * (n + 2))),
        UInt256.ofNat (32 * (n + 2)), cacheWord]) := by
  have hsum : 32 + 32 * (n + 1) = 32 * (n + 2) := by omega
  simp [advancePrefix, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, checked, atPC, hrun, hsum,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_tailPrefix (s : State) (input : ByteArray)
    (hinput : s.executionEnv.calldata = input) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock tailPrefix (tailEntry s) =
      some (atPC s 3223 [1006,
        UInt256.xor tailWord (MachineState.readWord input 992)]) := by
  simp [tailPrefix, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, tailEntry, atPC, hinput, hrun, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_failPrefix (s : State) (offset : UInt256) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock (failPath.take 4) (failEntry s offset) =
      some (atPC s 3257 [1006]) := by
  simp [failPath, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, failEntry, atPC, hrun,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_notAPrefix (s : State) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock (notAPath.take 3) (notAEntry s) =
      some (atPC s 3263 [1696, 1000]) := by
  simp [notAPath, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, notAEntry, atPC, hrun,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Ripemd160.Submission.H39Memo.A1000
