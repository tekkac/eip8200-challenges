import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSwapLemmas
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word
import Challenge.EvmProof.Stepper
import YulEvmCompiler.Instr

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

/-!
# Raw execution of the 419d031 consume tail

Artifact-independent. `consumeBody` is the frozen candidate sequence from
PC `0x9a9` through the earlier `JUMP` at `0x9fb`. Nine following `STOP`
bytes are unreachable padding and are not executed.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailConsume

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSwapLemmas
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

/-- Frozen candidate bytes at `0x9a9 .. 0x9fc` inclusive. -/
def consumeBodyBytes : List UInt8 :=
  [0x92, 0x90, 0x96, 0x60, 0x40, 0x51, 0x01, 0x01, 0x63, 0xff, 0xff, 0xff, 0xff,
   0x16, 0x92, 0x90, 0x96, 0x60, 0x60, 0x51, 0x01, 0x01, 0x63, 0xff, 0xff, 0xff,
   0xff, 0x16, 0x60, 0x40, 0x52, 0x90, 0x95, 0x60, 0x80, 0x51, 0x01, 0x01, 0x63,
   0xff, 0xff, 0xff, 0xff, 0x16, 0x60, 0x60, 0x52, 0x94, 0x90, 0x91, 0x60, 0xa0,
   0x51, 0x01, 0x01, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x60, 0x80, 0x52,
   0x60, 0x20, 0x51, 0x01, 0x01, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x60, 0xa0,
   0x52, 0x60, 0x20, 0x52, 0x50, 0x56]

@[simp] theorem consumeBodyBytes_length : consumeBodyBytes.length = 83 := by
  rfl

set_option linter.unusedSimpArgs false in
theorem consumeBody_bytes :
    assembleBytes consumeBody = consumeBodyBytes := by
  simp [consumeBody, quadTailBeforeJumpTemplate, c0Instructions, c1Instructions,
    c2Instructions, c3Instructions, c4Instructions, storeH0Instructions,
    cleanupInstructions, consumeBodyBytes, swap5H, swap6H, swap7H,
    swap1, swap2, swap3, op, push1, push4, mask, assembleBytes_cons,
    assembleBytes_nil, Instr.bytes, Instr.opByte, natToBE]

/-- Same `runInstrSeq` shape as `StackRoundTrace`: halt stays `Running`
between instructions; the last instruction may `JUMP`. -/
def runInstrSeq : List Instr → State → Option State
  | [], s => some s
  | instruction :: rest, s =>
      match Challenge.EvmProof.Stepper.runInstr instruction s with
      | none => none
      | some next =>
          match rest with
          | [] => some next
          | _ :: _ =>
              match next.halt with
              | .Running => runInstrSeq rest next
              | _ => none

abbrev consumeResult := QuadTailTemplate.finalResult

private theorem activeWordsAfter_tail (s : State) (offset : Nat)
    (hoff : offset + 32 ≤ 66 * 32)
    (hactive : 66 ≤ s.activeWords.toNat) :
    s.activeWordsAfterUInt256 offset 32 = s.activeWords := by
  unfold State.activeWordsAfterUInt256
  have haw : MachineState.activeWordsAfter s.activeWords.toNat offset 32 =
      s.activeWords.toNat := by
    unfold MachineState.activeWordsAfter
    rw [if_neg (by decide : (32 : Nat) ≠ 0)]
    apply Nat.max_eq_left
    have hq : (offset + 32 - 1) / 32 < s.activeWords.toNat := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    omega
  rw [haw]
  cases hword : s.activeWords with
  | mk val =>
      apply congrArg UInt256.mk
      apply Fin.ext
      simp [UInt256.toNat, Fin.ofNat, Nat.mod_eq_of_lt val.isLt]

private theorem readWord_writeHashWord_disjoint (memory : ByteArray)
    (readStart writeStart value : Nat)
    (hdisjoint : readStart + 32 ≤ writeStart ∨
      writeStart + 32 ≤ readStart) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) writeStart)
        readStart = MachineState.readWord memory readStart := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  have hsize :
      (Data.Bytes.natToBytesPadded value 32).size = 32 := by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  rw [hsize]
  exact hdisjoint

private theorem read96_write64 (memory : ByteArray) (value : Nat) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) 64) 96 =
      MachineState.readWord memory 96 := by
  exact readWord_writeHashWord_disjoint _ _ _ _ (Or.inr (by omega))

private theorem read128_write64 (memory : ByteArray) (value : Nat) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) 64) 128 =
      MachineState.readWord memory 128 := by
  exact readWord_writeHashWord_disjoint _ _ _ _ (Or.inr (by omega))

private theorem read128_write96 (memory : ByteArray) (value : Nat) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) 96) 128 =
      MachineState.readWord memory 128 := by
  exact readWord_writeHashWord_disjoint _ _ _ _ (Or.inr (by omega))

private theorem read160_write64 (memory : ByteArray) (value : Nat) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) 64) 160 =
      MachineState.readWord memory 160 := by
  exact readWord_writeHashWord_disjoint _ _ _ _ (Or.inr (by omega))

private theorem read160_write96 (memory : ByteArray) (value : Nat) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) 96) 160 =
      MachineState.readWord memory 160 := by
  exact readWord_writeHashWord_disjoint _ _ _ _ (Or.inr (by omega))

private theorem read160_write128 (memory : ByteArray) (value : Nat) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) 128) 160 =
      MachineState.readWord memory 160 := by
  exact readWord_writeHashWord_disjoint _ _ _ _ (Or.inr (by omega))

private theorem read32_write64 (memory : ByteArray) (value : Nat) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) 64) 32 =
      MachineState.readWord memory 32 := by
  exact readWord_writeHashWord_disjoint _ _ _ _ (Or.inl (by omega))

private theorem read32_write96 (memory : ByteArray) (value : Nat) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) 96) 32 =
      MachineState.readWord memory 32 := by
  exact readWord_writeHashWord_disjoint _ _ _ _ (Or.inl (by omega))

private theorem read32_write128 (memory : ByteArray) (value : Nat) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) 128) 32 =
      MachineState.readWord memory 32 := by
  exact readWord_writeHashWord_disjoint _ _ _ _ (Or.inl (by omega))

private theorem read32_write160 (memory : ByteArray) (value : Nat) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) 160) 32 =
      MachineState.readWord memory 32 := by
  exact readWord_writeHashWord_disjoint _ _ _ _ (Or.inl (by omega))

private theorem mask32_push (value : UInt256) :
    UInt256.land (UInt256.ofNat 0xffffffff) value = mask32 value := by
  unfold mask32
  exact Challenge.Ripemd160.Submission.Proofs.Bytecode.Word.land_comm
    (UInt256.ofNat 0xffffffff) value

private theorem add3_comm_right (a b c : UInt256) : a + b + c = a + c + b := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_add, Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_add, Challenge.EvmProof.Word.word_toNat_add]
  have hmod (x y z : Nat) :
      ((x + y) % 2 ^ 256 + z) % 2 ^ 256 = (x + y + z) % 2 ^ 256 := by
    rw [Nat.mod_add_mod]
  rw [hmod, hmod]
  simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem tailCapacity (rho : List UInt256) (hstack : rho.length < 1007)
    (m : Nat) (hm : m ≤ 16) : rho.length + m < 1024 := by
  omega

set_option linter.unusedSimpArgs false in
/-- Universal raw execution on the cached-factor rotated-left stack. -/
theorem run_consumeBody (s : State)
    (left right : Compression.EvmWorking) (ret : UInt256)
    (rest : List UInt256)
    (hrun : s.halt = .Running)
    (_hfork : s.fork = .Osaka)
    (hactive : 66 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1007)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    runInstrSeq consumeBody (tailEntry s left right ret rest) =
      some (finalResult s left right ret rest) := by
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hcap6 : rest.length + 6 < 1024 := by omega
  have hcap7 : rest.length + 7 < 1024 := by omega
  have hcap8 : rest.length + 8 < 1024 := by omega
  have hcap9 : rest.length + 9 < 1024 := by omega
  have hcap10 : rest.length + 10 < 1024 := by omega
  have hcap11 : rest.length + 11 < 1024 := by omega
  have hcap12 : rest.length + 12 < 1024 := by omega
  have hcap13 : rest.length + 13 < 1024 := by omega
  have hcap14 : rest.length + 14 < 1024 := by omega
  have hcap15 : rest.length + 15 < 1024 := by omega
  have hcap16 : rest.length + 16 < 1024 := by omega
  simp (config := { maxSteps := 1000000 }) (discharger := omega)
    [runInstrSeq, consumeBody, quadTailBeforeJumpTemplate,
      c0Instructions, c1Instructions, c2Instructions, c3Instructions,
      c4Instructions, storeH0Instructions, cleanupInstructions,
      swap5H, swap6H, swap7H, swap1, swap2, swap3, op, push1, push4, mask,
      tailEntry, workingStack, tailStartPC, tailJumpPC, factor,
      finalResult, beforeJumpResult, StackTail.preJumpResult, StackTail.combined,
      Challenge.EvmProof.Stepper.runInstr, StackMemory.storeHash,
      activeWordsAfter_tail, readWord_writeHashWord_disjoint,
      read96_write64, read128_write64, read128_write96, read160_write64,
      read160_write96, read160_write128, read32_write64, read32_write96,
      read32_write128, read32_write160, mask32_push,
      exchange_swap1, exchange_swap2, exchange_swap3, exchange_swap5,
      exchange_swap6, exchange_swap7, hrun, hactive, hstack, hvalid,
      hcap0, hcap1, hcap2, hcap3, hcap4, hcap5, hcap6, hcap7, hcap8, hcap9,
      hcap10, hcap11, hcap12, hcap13, hcap14, hcap15, hcap16, Nat.add_assoc,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      Challenge.EvmProof.Word.mask32_toNat, Compression.evmCombine,
      StackMemory.hashAt]
  have horder (a : UInt256) : a + right.b + left.a = a + left.a + right.b := by
    change UInt256.mk ((a.val + right.b.val) + left.a.val) =
      UInt256.mk ((a.val + left.a.val) + right.b.val)
    congr 1
    exact add_right_comm _ _ _
  simp only [horder]

set_option linter.unusedSimpArgs false in
theorem runTail_consumeBody (s : State)
    (left right : Compression.EvmWorking) (ret : UInt256)
    (rest : List UInt256)
    (hactive : 66 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1007)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    StackTail.runTailInstrs consumeBody (tailEntry s left right ret rest) =
      some (finalResult s left right ret rest) := by
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hcap6 : rest.length + 6 < 1024 := by omega
  have hcap7 : rest.length + 7 < 1024 := by omega
  have hcap8 : rest.length + 8 < 1024 := by omega
  have hcap9 : rest.length + 9 < 1024 := by omega
  have hcap10 : rest.length + 10 < 1024 := by omega
  have hcap11 : rest.length + 11 < 1024 := by omega
  have hcap12 : rest.length + 12 < 1024 := by omega
  have hcap13 : rest.length + 13 < 1024 := by omega
  have hcap14 : rest.length + 14 < 1024 := by omega
  have hcap15 : rest.length + 15 < 1024 := by omega
  have hcap16 : rest.length + 16 < 1024 := by omega
  simp (config := { maxSteps := 1000000 }) (discharger := omega)
    [StackTail.runTailInstrs, consumeBody, quadTailBeforeJumpTemplate,
      c0Instructions, c1Instructions, c2Instructions, c3Instructions,
      c4Instructions, storeH0Instructions, cleanupInstructions,
      swap5H, swap6H, swap7H, swap1, swap2, swap3, op, push1, push4, mask,
      tailEntry, workingStack, tailStartPC, tailJumpPC, factor,
      finalResult, beforeJumpResult, StackTail.preJumpResult, StackTail.combined,
      Challenge.EvmProof.Stepper.runInstr, StackMemory.storeHash,
      activeWordsAfter_tail, readWord_writeHashWord_disjoint,
      read96_write64, read128_write64, read128_write96, read160_write64,
      read160_write96, read160_write128, read32_write64, read32_write96,
      read32_write128, read32_write160, mask32_push,
      exchange_swap1, exchange_swap2, exchange_swap3, exchange_swap5,
      exchange_swap6, exchange_swap7, hactive, hstack, hvalid,
      hcap0, hcap1, hcap2, hcap3, hcap4, hcap5, hcap6, hcap7, hcap8, hcap9,
      hcap10, hcap11, hcap12, hcap13, hcap14, hcap15, hcap16, Nat.add_assoc,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      Challenge.EvmProof.Word.mask32_toNat, Compression.evmCombine,
      StackMemory.hashAt]
  have horder (a : UInt256) : a + right.b + left.a = a + left.a + right.b := by
    change UInt256.mk ((a.val + right.b.val) + left.a.val) =
      UInt256.mk ((a.val + left.a.val) + right.b.val)
    congr 1
    exact add_right_comm _ _ _
  simp only [horder]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailConsume
