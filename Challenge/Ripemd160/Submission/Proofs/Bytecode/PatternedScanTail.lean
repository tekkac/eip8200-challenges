import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# The padded tail word and the miss test

Bytes 992 to 999 are read as a whole word, so the constant is shifted up to
meet the zero padding. A hit falls directly into the stored-digest return while
retaining the inert scanner frame. A miss branches to former guard filler,
clears that frame, and rejoins the generic implementation with an empty stack.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec PatternedSwar

theorem hdest1006 : Decode.isValidJumpDest submissionBytecode 1006 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 682 (by rfl)

theorem hdest4935 : Decode.isValidJumpDest submissionBytecode 4935 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 2864 (by rfl)

def tailCondition (input : ByteArray) (acc : UInt256) : UInt256 :=
  UInt256.lor acc
    (UInt256.xor
      (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256))
      (MachineState.readWord input ((992 : UInt256)).toNat))

private def gasSteps_tail_prefix_sym (input : ByteArray) (sv ov acc : UInt256) :
    GasSteps (stS input 5203 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 5222 [tailCondition input acc, sv, ov, acc, P7, M, m7, P, m8]) := by
  have step2962 := soundS (pushAt 2962 2 0x03e0)
    (blockOfS _ (pcFactS input 2962 5203 [sv, ov, acc, P7, M, m7, P, m8]
      (by norm_num) pc2962)
      (stepS_push input 5203 2 (992 : UInt256)
        [sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide)
        (by norm_num)))
  have step2963 := soundS (opAt 2963 .CALLDATALOAD)
    (blockOfS _ (pcFactS input 2963 5206
      [(992 : UInt256), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2963)
      (stepS_calldataload input 5206 (992 : UInt256)
        [sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2964 := soundS (pushAt 2964 8 0x88add2f71c41668b)
    (blockOfS _ (pcFactS input 2964 5207
      [MachineState.readWord input ((992 : UInt256)).toNat,
       sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2964)
      (stepS_push input 5207 8 (0x88add2f71c41668b : UInt256)
        [MachineState.readWord input ((992 : UInt256)).toNat,
         sv, ov, acc, P7, M, m7, P, m8]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step2965 := soundS (pushAt 2965 1 0xc0)
    (blockOfS _ (pcFactS input 2965 5216
      [(0x88add2f71c41668b : UInt256),
       MachineState.readWord input ((992 : UInt256)).toNat,
       sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2965)
      (stepS_push input 5216 1 (192 : UInt256)
        [(0x88add2f71c41668b : UInt256),
         MachineState.readWord input ((992 : UInt256)).toNat,
         sv, ov, acc, P7, M, m7, P, m8]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step2966 := soundS (opAt 2966 .SHL)
    (blockOfS _ (pcFactS input 2966 5218
      [(192 : UInt256), (0x88add2f71c41668b : UInt256),
       MachineState.readWord input ((992 : UInt256)).toNat,
       sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2966)
      (stepS_shl input 5218 (192 : UInt256)
        (0x88add2f71c41668b : UInt256)
        [MachineState.readWord input ((992 : UInt256)).toNat,
         sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2967 := soundS (opAt 2967 .XOR)
    (blockOfS _ (pcFactS input 2967 5219
      [UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256),
       MachineState.readWord input ((992 : UInt256)).toNat,
       sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2967)
      (stepS_xor input 5219
        (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256))
        (MachineState.readWord input ((992 : UInt256)).toNat)
        [sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2968 := soundS (opAt 2968 (.Dup ⟨3, by decide⟩))
    (blockOfS _ (pcFactS input 2968 5220
      [UInt256.xor
        (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256))
        (MachineState.readWord input ((992 : UInt256)).toNat),
       sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2968)
      (stepS_dup input 5220 3 (by decide)
        [UInt256.xor
          (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256))
          (MachineState.readWord input ((992 : UInt256)).toNat),
         sv, ov, acc, P7, M, m7, P, m8]
        acc (by rfl) (by simp) (by norm_num)))
  have step2969 := soundS (opAt 2969 .OR)
    (blockOfS _ (pcFactS input 2969 5221
      [acc,
       UInt256.xor
        (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256))
        (MachineState.readWord input ((992 : UInt256)).toNat),
       sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2969)
      (stepS_or input 5221 acc
        (UInt256.xor
          (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256))
          (MachineState.readWord input ((992 : UInt256)).toNat))
        [sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  exact step2962.trans (step2963.trans (step2964.trans (step2965.trans
    (step2966.trans (step2967.trans (step2968.trans step2969))))))

private def gasSteps_cleanup_sym (input : ByteArray) (sv ov acc : UInt256) :
    GasSteps (stS input 4935 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 1006 []) := by
  have step2864 := soundS (opAt 2864 .JUMPDEST)
    (blockOfS _ (pcFactS input 2864 4935
      [sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2864)
      (stepS_jumpdest input 4935 [sv, ov, acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have step2865 := soundS (opAt 2865 .POP)
    (blockOfS _ (pcFactS input 2865 4936
      [sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2865)
      (stepS_pop input 4936 sv [ov, acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have step2866 := soundS (opAt 2866 .POP)
    (blockOfS _ (pcFactS input 2866 4937
      [ov, acc, P7, M, m7, P, m8] (by norm_num) pc2866)
      (stepS_pop input 4937 ov [acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have step2867 := soundS (opAt 2867 .POP)
    (blockOfS _ (pcFactS input 2867 4938
      [acc, P7, M, m7, P, m8] (by norm_num) pc2867)
      (stepS_pop input 4938 acc [P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have step2868 := soundS (opAt 2868 .POP)
    (blockOfS _ (pcFactS input 2868 4939
      [P7, M, m7, P, m8] (by norm_num) pc2868)
      (stepS_pop input 4939 P7 [M, m7, P, m8] (by simp) (by norm_num)))
  have step2869 := soundS (opAt 2869 .POP)
    (blockOfS _ (pcFactS input 2869 4940
      [M, m7, P, m8] (by norm_num) pc2869)
      (stepS_pop input 4940 M [m7, P, m8] (by simp) (by norm_num)))
  have step2870 := soundS (opAt 2870 .POP)
    (blockOfS _ (pcFactS input 2870 4941
      [m7, P, m8] (by norm_num) pc2870)
      (stepS_pop input 4941 m7 [P, m8] (by simp) (by norm_num)))
  have step2871 := soundS (opAt 2871 .POP)
    (blockOfS _ (pcFactS input 2871 4942 [P, m8] (by norm_num) pc2871)
      (stepS_pop input 4942 P [m8] (by simp) (by norm_num)))
  have step2872 := soundS (opAt 2872 .POP)
    (blockOfS _ (pcFactS input 2872 4943 [m8] (by norm_num) pc2872)
      (stepS_pop input 4943 m8 [] (by simp) (by norm_num)))
  have step2873 := soundS (pushAt 2873 2 0x03ee)
    (blockOfS _ (pcFactS input 2873 4944 [] (by norm_num) pc2873)
      (stepS_push input 4944 2 (1006 : UInt256) []
        (by simp) (by decide) (by decide) (by norm_num)))
  have step2874 := soundS (opAt 2874 .JUMP)
    (blockOfS _ (pcFactS input 2874 4947 [(1006 : UInt256)]
      (by norm_num) pc2874)
      (stepS_jump input 4947 1006 (1006 : UInt256) []
        (by simp) (by norm_num) rfl hdest1006))
  exact step2864.trans (step2865.trans (step2866.trans (step2867.trans
    (step2868.trans (step2869.trans (step2870.trans (step2871.trans
      (step2872.trans (step2873.trans step2874))))))))))

/-- The accumulator is zero, so the guard falls directly into the return. -/
def gasSteps_tail_hit_sym (input : ByteArray) (sv ov acc : UInt256)
    (hc : ¬ UInt256.isTrue (tailCondition input acc)) :
    GasSteps (stS input 5203 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 5226 [sv, ov, acc, P7, M, m7, P, m8]) := by
  have step2970 := soundS (pushAt 2970 2 0x1347)
    (blockOfS _ (pcFactS input 2970 5222
      [tailCondition input acc, sv, ov, acc, P7, M, m7, P, m8]
      (by norm_num) pc2970)
      (stepS_push input 5222 2 (4935 : UInt256)
        [tailCondition input acc, sv, ov, acc, P7, M, m7, P, m8]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step2971 := soundS (opAt 2971 .JUMPI)
    (blockOfS _ (pcFactS input 2971 5225
      [(4935 : UInt256), tailCondition input acc,
       sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2971)
      (stepS_jumpi_fall input 5225 (4935 : UInt256)
        (tailCondition input acc) [sv, ov, acc, P7, M, m7, P, m8]
        (by simp) (by norm_num) hc))
  exact (gasSteps_tail_prefix_sym input sv ov acc).trans
    (step2970.trans step2971)

/-- A nonzero accumulator branches to the cleanup before the generic program. -/
def gasSteps_tail_miss_sym (input : ByteArray) (sv ov acc : UInt256)
    (hc : UInt256.isTrue (tailCondition input acc)) :
    GasSteps (stS input 5203 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 1006 []) := by
  have step2970 := soundS (pushAt 2970 2 0x1347)
    (blockOfS _ (pcFactS input 2970 5222
      [tailCondition input acc, sv, ov, acc, P7, M, m7, P, m8]
      (by norm_num) pc2970)
      (stepS_push input 5222 2 (4935 : UInt256)
        [tailCondition input acc, sv, ov, acc, P7, M, m7, P, m8]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step2971 := soundS (opAt 2971 .JUMPI)
    (blockOfS _ (pcFactS input 2971 5225
      [(4935 : UInt256), tailCondition input acc,
       sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2971)
      (stepS_jumpi_taken input 5225 4935 (4935 : UInt256)
        (tailCondition input acc) [sv, ov, acc, P7, M, m7, P, m8]
        (by simp) (by norm_num) rfl hc hdest4935))
  exact (gasSteps_tail_prefix_sym input sv ov acc).trans
    (step2970.trans (step2971.trans (gasSteps_cleanup_sym input sv ov acc)))

/-- The accumulator once the padded tail word has been folded in. -/
def scanAccFinal (input : ByteArray) : UInt256 :=
  UInt256.lor (scanAcc input 31)
    (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256))
      (MachineState.readWord input 992))

theorem isTrue_iff (x : UInt256) : UInt256.isTrue x ↔ x ≠ 0 := by
  unfold UInt256.isTrue
  have hz : (0 : UInt256).toNat = 0 := by decide
  exact ⟨fun h hx => h (by rw [hx, hz]),
    fun h hx => h (Challenge.EvmProof.Word.word_ext (by rw [hx, hz]))⟩

private theorem tail_read (input : ByteArray) :
    MachineState.readWord input ((992 : UInt256)).toNat =
      MachineState.readWord input 992 := by
  rw [show ((992 : UInt256)).toNat = 992 from by decide]

private theorem tail_state_eq (input : ByteArray) :
    tailState input (scanAcc input 31) =
      stS input 5203 [UInt256.ofNat (scalarAt 31), UInt256.ofNat 992,
        scanAcc input 31, P7, M, m7, P, m8] := rfl

/-- A zero accumulator means the calldata is the vector, so the guard answers. -/
def gasSteps_tail_hit (input : ByteArray) (hz : scanAccFinal input = 0) :
    GasSteps (tailState input (scanAcc input 31)) (hitState input) := by
  have hc : ¬ UInt256.isTrue (UInt256.lor (scanAcc input 31)
      (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256))
        (MachineState.readWord input ((992 : UInt256)).toNat))) := by
    rw [tail_read, isTrue_iff]
    exact fun h => h hz
  rw [tail_state_eq, show hitState input = stS input 5237 [] from rfl]
  exact gasSteps_tail_hit_sym input (UInt256.ofNat (scalarAt 31))
    (UInt256.ofNat 992) (scanAcc input 31) hc

/-- A nonzero accumulator means the program has to run. -/
def gasSteps_tail_miss (input : ByteArray) (hnz : scanAccFinal input ≠ 0) :
    GasSteps (tailState input (scanAcc input 31)) (fallbackState input) := by
  have hc : UInt256.isTrue (UInt256.lor (scanAcc input 31)
      (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256))
        (MachineState.readWord input ((992 : UInt256)).toNat))) := by
    rw [tail_read, isTrue_iff]
    exact hnz
  rw [tail_state_eq, show fallbackState input = stS input 1006 [] from rfl]
  exact gasSteps_tail_miss_sym input (UInt256.ofNat (scalarAt 31))
    (UInt256.ofNat 992) (scanAcc input 31) hc

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
