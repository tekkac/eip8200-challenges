import Challenge.Modexp.Submission.Proofs.Bytecode.BigComplete
import Challenge.Modexp.Submission.Proofs.Bytecode.WordCorrect
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
/-! # Functional correctness of multi-limb exponentiation -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentCorrect

open EvmSemantics
open EvmSemantics.EVM

open BigExponent

theorem exponentBit_toNat_le_one (byte : UInt256) (j : Nat) :
    (exponentBit byte j).toNat ≤ 1 := by
  rw [exponentBit, Challenge.EvmProof.Word.word_toNat_land,
    show (1 : UInt256).toNat = 1 by decide]
  exact Nat.and_le_right

theorem selectOffset_eq (ptr k : Nat) (hfit : ptr + 32 * k < 2 ^ 256) :
    (UInt256.ofNat ptr + selectOffset k).toNat = ptr + 32 * k := by
  rw [selectOffset]
  have hcomm : UInt256.ofNat ptr +
      UInt256.shiftLeft (UInt256.ofNat k) (UInt256.ofNat 5) =
      BigHelpers.clearOffset (UInt256.ofNat ptr) k := by
    simpa only [BigHelpers.clearOffset] using
      (Challenge.EvmProof.Word.word_add_comm (UInt256.ofNat ptr)
        (UInt256.shiftLeft (UInt256.ofNat k) (UInt256.ofNat 5)))
  rw [hcomm, BigHelpers.clearOffset_toNat ptr k hfit]

theorem selectMemory_zero (memory : ByteArray) (count : Nat)
    (hcount : count ≤ 32) :
    selectMemory memory (0 - UInt256.ofNat 0) count =
      BigHelpers.copyMemory memory (UInt256.ofNat 2048) (UInt256.ofNat 2048)
        count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [selectMemory, BigHelpers.copyMemory, ih (by omega)]
      simp only [selectedWord]
      have hz : (0 : UInt256) = UInt256.ofNat 0 := by decide
      rw [hz]
      rw [WordCorrect.select_zero]
      have h2048 : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
      rw [h2048]
      rw [selectOffset_eq 2048 count (by omega),
        BigHelpers.clearOffset_toNat 2048 count (by omega)]

theorem selectMemory_one (memory : ByteArray) (count : Nat)
    (hcount : count ≤ 32) :
    selectMemory memory (0 - UInt256.ofNat 1) count =
      BigHelpers.copyMemory memory (UInt256.ofNat 2048) (UInt256.ofNat 3072)
        count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [selectMemory, BigHelpers.copyMemory, ih (by omega)]
      simp only [selectedWord]
      have hz : (0 : UInt256) = UInt256.ofNat 0 := by decide
      rw [hz]
      rw [WordCorrect.select_one]
      have h2048 : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
      have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
      rw [h2048, h3072]
      rw [selectOffset_eq 3072 count (by omega),
        BigHelpers.clearOffset_toNat 3072 count (by omega),
        selectOffset_eq 2048 count (by omega),
        BigHelpers.clearOffset_toNat 2048 count (by omega)]

theorem readWord_copyMemory_self (memory : ByteArray) (ptr count j : Nat)
    (hj : j < count) (hfit : ptr + 32 * count < 2 ^ 256) :
    MachineState.readWord
        (BigHelpers.copyMemory memory (UInt256.ofNat ptr)
          (UInt256.ofNat ptr) count) (ptr + 32 * j) =
      MachineState.readWord memory (ptr + 32 * j) := by
  induction count with
  | zero => omega
  | succ count ih =>
      rw [BigHelpers.copyMemory]
      by_cases hjlast : j = count
      · subst j
        rw [BigHelpers.clearOffset_toNat ptr count (by omega),
          Challenge.EvmProof.Memory.readWord_writeWord]
        by_cases hzero : count = 0
        · subst count
          rfl
        · exact BigHelpers.readWord_copyMemory_disjoint_region memory ptr ptr
            (ptr + 32 * count) count count 0 (by omega) (by omega)
            (by omega) (Or.inl (by omega))
      · rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
        · exact ih (by omega) (by omega)
        · left
          rw [BigHelpers.clearOffset_toNat ptr count (by omega)]
          omega

theorem copyMemory_self_represents (memory : ByteArray) (ptr count value : Nat)
    (hfit : ptr + 32 * count < 2 ^ 256)
    (hrep : Limbs.Represents memory ptr count value) :
    Limbs.Represents
      (BigHelpers.copyMemory memory (UInt256.ofNat ptr) (UInt256.ofNat ptr)
        count) ptr count value := by
  refine ⟨hrep.1, ?_⟩
  rw [← hrep.2]
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro j hj
  exact congrArg UInt256.toNat
    (readWord_copyMemory_self memory ptr count j (by simpa using hj) hfit)

theorem selectMemory_represents (memory : ByteArray) (byte : UInt256)
    (j count square product : Nat) (hcount : count ≤ 32)
    (hsquare : Limbs.Represents memory 2048 count square)
    (hproduct : Limbs.Represents memory 3072 count product) :
    Limbs.Represents
      (selectMemory memory (selectMask byte j) count) 2048 count
      (if (exponentBit byte j).toNat = 0 then square else product) := by
  have hbit := exponentBit_toNat_le_one byte j
  have hword : UInt256.ofNat (exponentBit byte j).toNat =
      exponentBit byte j := WordCorrect.ofNat_toNat _
  interval_cases h : (exponentBit byte j).toNat
  · simp only [if_pos rfl]
    rw [selectMask, ← hword, selectMemory_zero memory count hcount]
    exact copyMemory_self_represents memory 2048 count square (by omega) hsquare
  · rw [selectMask, ← hword, selectMemory_one memory count hcount]
    exact BigHelpers.copyMemory_represents memory 2048 3072 count product
      hproduct (by omega) (by omega) (Or.inl (by omega))

theorem selectMemory_preserves_region (memory : ByteArray) (byte : UInt256)
    (j count ptr value : Nat) (hcount : count ≤ 32)
    (hptr : 2048 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 2048)
    (hrep : Limbs.Represents memory ptr count value) :
    Limbs.Represents (selectMemory memory (selectMask byte j) count)
      ptr count value := by
  have hbit := exponentBit_toNat_le_one byte j
  have hword : UInt256.ofNat (exponentBit byte j).toNat =
      exponentBit byte j := WordCorrect.ofNat_toNat _
  interval_cases h : (exponentBit byte j).toNat
  · rw [selectMask, ← hword, selectMemory_zero memory count hcount]
    exact BigHelpers.represents_copyMemory_disjoint_region memory 2048 2048
      ptr count value (by omega) hptr hrep
  · rw [selectMask, ← hword, selectMemory_one memory count hcount]
    exact BigHelpers.represents_copyMemory_disjoint_region memory 2048 3072
      ptr count value (by omega) hptr hrep

theorem mulOuterProgress_preserves_region (current : State) (a b : UInt256)
    (count steps ptr value : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hsteps : steps ≤ count) (hcount : count ≤ 32)
    (hptrOut : 3072 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 3072)
    (hptrAddend : 4096 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 4096)
    (hptrCandidate : ptr + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ ptr)
    (hrep : Limbs.Represents current.memory ptr count value) :
    Limbs.Represents
      (BigMul.mulOuterProgress current a b (UInt256.ofNat 3072)
        (UInt256.ofNat 0) count returnDest rest steps).memory
      ptr count value := by
  induction steps with
  | zero => simpa [BigMul.mulOuterProgress] using hrep
  | succ steps ih =>
      let before := BigMul.mulOuterProgress current a b (UInt256.ofNat 3072)
        (UInt256.ofNat 0) count returnDest rest steps
      let loaded := BigMul.mulLoadedState before b steps
      let word := BigMul.mulLoadedWord before b steps
      have hbefore : Limbs.Represents before.memory ptr count value :=
        ih (by omega)
      have hloaded : Limbs.Represents loaded.memory ptr count value := by
        simpa [loaded, BigMul.mulLoadedState] using hbefore
      simpa [BigMul.mulOuterProgress, before, loaded, word] using
        BigMul.mulWordProgress_preserves_region loaded word a b count steps
          256 ptr value returnDest rest (by omega) hcount hptrOut hptrAddend
          hptrCandidate hloaded

theorem mulResult_preserves_region (s : State) (a b : UInt256)
    (count ptr value : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcount : count ≤ 32)
    (hptrOut : 3072 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 3072)
    (hptrAddend : 4096 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 4096)
    (hptrCandidate : ptr + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ ptr)
    (hrep : Limbs.Represents s.memory ptr count value) :
    Limbs.Represents
      (mulResult s a b (UInt256.ofNat 3072) (UInt256.ofNat 0) count
        returnDest rest).memory ptr count value := by
  let cleared := BigMul.mulAfterClear s a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count returnDest rest
  let copied := BigMul.mulAfterCopy s a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count returnDest rest
  have hcleared : Limbs.Represents cleared.memory ptr count value := by
    simpa [cleared, BigMul.mulAfterClear] using
      BigHelpers.represents_clearMemory_disjoint_region s.memory 3072 ptr
        count value (by omega) hptrOut hrep
  have hcopied : Limbs.Represents copied.memory ptr count value := by
    simpa [copied, BigMul.mulAfterCopy, cleared,
      WordCorrect.ofNat_toNat a] using
      BigHelpers.represents_copyMemory_disjoint_region cleared.memory 4096
        a.toNat ptr count value (by omega) hptrAddend hcleared
  have hprogress := mulOuterProgress_preserves_region copied a b count count
    ptr value returnDest rest (by omega) hcount hptrOut hptrAddend
    hptrCandidate hcopied
  simpa [mulResult, copied, BigMul.mulReturned] using hprogress

def bitStepValue (modulus : Nat) (byte : UInt256) (j acc base : Nat) : Nat :=
  let square := (acc * acc) % modulus
  if (exponentBit byte j).toNat = 0 then square
  else (square * base) % modulus

theorem selectProgress_represents_bitStep (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) (acc base modulus : Nat)
    (hcount : count ≤ 32) (hmodulusPos : 0 < modulus)
    (haccReduced : acc < modulus)
    (hacc : Limbs.Represents s.memory 2048 count acc)
    (hbase : Limbs.Represents s.memory 1024 count base)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    Limbs.Represents
        (selectProgress s accumulatorWord count b e m baseOff expOff i j offset
          byte rest count).memory 2048 count
        (bitStepValue modulus byte j acc base) ∧
      Limbs.Represents
        (selectProgress s accumulatorWord count b e m baseOff expOff i j offset
          byte rest count).memory 1024 count base ∧
      Limbs.Represents
        (selectProgress s accumulatorWord count b e m baseOff expOff i j offset
          byte rest count).memory 0 count modulus := by
  let body := innerBody s accumulatorWord count b e m baseOff expOff i offset
    byte rest j
  let frame := bitFrame accumulatorWord count b e m baseOff expOff i j offset
    byte (exponentBit byte j) rest
  let squared := squareReturned s accumulatorWord count b e m baseOff expOff i
    j offset byte rest
  let copied := copiedSquare s accumulatorWord count b e m baseOff expOff i j
    offset byte rest
  let product := productReturned s accumulatorWord count b e m baseOff expOff i
    j offset byte rest
  let squareValue := (acc * acc) % modulus
  let productValue := (squareValue * base) % modulus
  have h0 : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have h1024 : (1024 : UInt256) = UInt256.ofNat 1024 := by decide
  have h2048 : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
  have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
  have h1000 : (1000 : UInt256) = UInt256.ofNat 1000 := by decide
  have h1015 : (1015 : UInt256) = UInt256.ofNat 1015 := by decide
  have h1034 : (1034 : UInt256) = UInt256.ofNat 1034 := by decide
  have hbodyAcc : Limbs.Represents body.memory 2048 count acc := by
    simpa [body, innerBody, innerLoop] using hacc
  have hbodyBase : Limbs.Represents body.memory 1024 count base := by
    simpa [body, innerBody, innerLoop] using hbase
  have hbodyModulus : Limbs.Represents body.memory 0 count modulus := by
    simpa [body, innerBody, innerLoop] using hmodulus
  have hsquare : Limbs.Represents squared.memory 3072 count squareValue := by
    simpa [squared, squareReturned, mulResult, body, frame, squareValue,
      h0, h2048, h3072, h1000] using
      BigMul.mulReturned_represents_product body 2048 count acc acc modulus
        (UInt256.ofNat 1000) frame hcount (by omega) hmodulusPos haccReduced
        hbodyAcc hbodyAcc hbodyModulus
  have hsquaredBase : Limbs.Represents squared.memory 1024 count base := by
    simpa [squared, squareReturned, body, frame, h0, h2048, h3072, h1000]
      using
      mulResult_preserves_region body (UInt256.ofNat 2048)
        (UInt256.ofNat 2048) count 1024 base (UInt256.ofNat 1000) frame hcount
        (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) hbodyBase
  have hsquaredModulus : Limbs.Represents squared.memory 0 count modulus := by
    simpa [squared, squareReturned, body, frame, h0, h2048, h3072, h1000]
      using
      mulResult_preserves_region body (UInt256.ofNat 2048)
        (UInt256.ofNat 2048) count 0 modulus (UInt256.ofNat 1000) frame hcount
        (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
        hbodyModulus
  have hcopiedSquare : Limbs.Represents copied.memory 2048 count squareValue := by
    simpa [copied, copiedSquare, BigHelpers.copyReturned, h2048, h3072,
      h1015] using
      BigHelpers.copyMemory_represents squared.memory 2048 3072 count
        squareValue hsquare (by omega) (by omega) (Or.inl (by omega))
  have hcopiedBase : Limbs.Represents copied.memory 1024 count base := by
    simpa [copied, copiedSquare, BigHelpers.copyReturned, h2048, h3072,
      h1015] using
      BigHelpers.represents_copyMemory_disjoint_region squared.memory 2048
        3072 1024 count base (by omega) (Or.inr (by omega)) hsquaredBase
  have hcopiedModulus : Limbs.Represents copied.memory 0 count modulus := by
    simpa [copied, copiedSquare, BigHelpers.copyReturned, h2048, h3072,
      h1015] using
      BigHelpers.represents_copyMemory_disjoint_region squared.memory 2048
        3072 0 count modulus (by omega) (Or.inr (by omega)) hsquaredModulus
  have hsquareReduced : squareValue < modulus := Nat.mod_lt _ hmodulusPos
  have hproduct : Limbs.Represents product.memory 3072 count productValue := by
    simpa [product, productReturned, mulResult, squareValue, productValue,
      frame, h0, h1024, h2048, h3072, h1034] using
      BigMul.mulReturned_represents_product copied 1024 count squareValue base
        modulus (UInt256.ofNat 1034) frame hcount (by omega) hmodulusPos
        hsquareReduced hcopiedSquare hcopiedBase hcopiedModulus
  have hproductBase : Limbs.Represents product.memory 1024 count base := by
    simpa [product, productReturned, mulResult, squareValue, frame, h0, h1024,
      h2048, h3072, h1034, BigMul.mulReturned] using
      (BigMul.mulOuterProgress_afterCopy_represents_product copied 1024 count
        squareValue base modulus (UInt256.ofNat 1034) frame hcount (by omega)
        hmodulusPos hsquareReduced hcopiedSquare hcopiedBase
        hcopiedModulus).2.1
  have hproductModulus : Limbs.Represents product.memory 0 count modulus := by
    simpa [product, productReturned, mulResult, squareValue, frame, h0, h1024,
      h2048, h3072, h1034, BigMul.mulReturned] using
      (BigMul.mulOuterProgress_afterCopy_represents_product copied 1024 count
        squareValue base modulus (UInt256.ofNat 1034) frame hcount (by omega)
        hmodulusPos hsquareReduced hcopiedSquare hcopiedBase
        hcopiedModulus).2.2
  have hselected := selectMemory_represents product.memory byte j count
    squareValue productValue hcount
    (by
      simpa [product, productReturned, squareValue, frame, h0, h1024, h2048,
        h3072, h1034] using
        mulResult_preserves_region copied (UInt256.ofNat 2048)
          (UInt256.ofNat 1024) count 2048 squareValue (UInt256.ofNat 1034)
          frame hcount (Or.inr (by omega)) (Or.inr (by omega))
          (Or.inl (by omega)) hcopiedSquare)
    hproduct
  have hselectedBase := selectMemory_preserves_region product.memory byte j
    count 1024 base hcount (Or.inr (by omega)) hproductBase
  have hselectedModulus := selectMemory_preserves_region product.memory byte j
    count 0 modulus hcount (Or.inr (by omega)) hproductModulus
  exact ⟨by
    simpa [selectProgress, product, bitStepValue, squareValue, productValue]
      using hselected,
    by simpa [selectProgress, product] using hselectedBase,
    by simpa [selectProgress, product] using hselectedModulus⟩

theorem exponentBit_toNat_eq (byte : UInt256) (j : Nat) (hj : j < 8) :
    (exponentBit byte j).toNat = WordCorrect.exponentBitNat byte j := by
  have h := congrArg UInt256.toNat (WordCorrect.exponentBit_eq byte j hj)
  have hbit := WordCorrect.exponentBitNat_zero_or_one byte j
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : WordCorrect.exponentBitNat byte j < 2 ^ 256)]
    at h
  exact h

theorem bitStepValue_eq_natBitStep (modulus : Nat) (byte : UInt256)
    (j acc base : Nat) (hj : j < 8) :
    bitStepValue modulus byte j acc base =
      WordCorrect.natBitStep modulus byte j acc base := by
  simp only [bitStepValue, WordCorrect.natBitStep]
  rw [exponentBit_toNat_eq byte j hj]

theorem exponentBitProgress_represents (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i : Nat)
    (offset byte : UInt256) (rest : List UInt256) (steps acc base modulus : Nat)
    (hsteps : steps ≤ 8) (hcount : count ≤ 32)
    (hmodulusPos : 0 < modulus) (haccReduced : acc < modulus)
    (hacc : Limbs.Represents s.memory 2048 count acc)
    (hbase : Limbs.Represents s.memory 1024 count base)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    let progress := BigExponent.exponentBitProgress s accumulatorWord count b e
      m baseOff expOff i offset byte rest steps
    Limbs.Represents progress.memory 2048 count
        (WordCorrect.natBitAfter modulus byte base steps acc) ∧
      Limbs.Represents progress.memory 1024 count base ∧
      Limbs.Represents progress.memory 0 count modulus := by
  induction steps with
  | zero => exact ⟨hacc, hbase, hmodulus⟩
  | succ steps ih =>
      let before := BigExponent.exponentBitProgress s accumulatorWord count b e
        m baseOff expOff i offset byte rest steps
      let beforeValue := WordCorrect.natBitAfter modulus byte base steps acc
      have hbefore := ih (by omega)
      have hbeforeReduced : beforeValue < modulus :=
        WordCorrect.natBitAfter_lt modulus byte base acc steps hmodulusPos
          haccReduced
      have hstep := selectProgress_represents_bitStep before accumulatorWord
        count b e m baseOff expOff i steps offset byte rest beforeValue base
        modulus hcount hmodulusPos hbeforeReduced hbefore.1 hbefore.2.1
        hbefore.2.2
      simpa [BigExponent.exponentBitProgress, before, beforeValue,
        WordCorrect.natBitAfter,
        bitStepValue_eq_natBitStep modulus byte steps beforeValue base
          (by omega)] using
        hstep

theorem natBitAfter_eight_eq_natExpStep (modulus : Nat) (byte : UInt256)
    (acc base : Nat) (hacc : acc < modulus) (hbyte : byte.toNat < 256) :
    WordCorrect.natBitAfter modulus byte base 8 acc =
      WordCorrect.natExpStep modulus byte acc base := by
  rw [WordCorrect.natBitAfter_eq modulus byte base acc 8 hacc,
    WordCorrect.bitPrefix_eight byte hbyte]
  norm_num [WordCorrect.natExpStep]

theorem loadedExponentByte_lt (s : State) (expOff i : Nat) :
    (loadedExponentByte s expOff i).toNat < 256 := by
  unfold loadedExponentByte UInt256.byteAt
  rw [show (0 : UInt256).toNat = 0 by decide]
  rw [if_neg (by omega)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  have hand :
      ((MachineState.readWord s.executionEnv.calldata (expOff + i)).toNat >>>
        (8 * (31 - 0))) &&& 255 ≤ 255 := Nat.and_le_right
  have hlt :
      ((MachineState.readWord s.executionEnv.calldata (expOff + i)).toNat >>>
        (8 * (31 - 0))) &&& 255 < 2 ^ 256 := by omega
  rw [Nat.mod_eq_of_lt hlt]
  omega

def exponentValueAfter (s : State) (modulus base expOff : Nat) :
    Nat → Nat → Nat
  | 0, acc => acc
  | i + 1, acc =>
      WordCorrect.natExpStep modulus (loadedExponentByte s expOff i)
        (exponentValueAfter s modulus base expOff i acc) base

theorem exponentValueAfter_lt (s : State) (modulus base expOff steps acc : Nat)
    (hmodulusPos : 0 < modulus) (hacc : acc < modulus) :
    exponentValueAfter s modulus base expOff steps acc < modulus := by
  induction steps with
  | zero => exact hacc
  | succ steps ih =>
      rw [exponentValueAfter, WordCorrect.natExpStep]
      exact Nat.mod_lt _ hmodulusPos

theorem exponentByteProgress_represents (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) (steps acc base modulus : Nat) (hsteps : steps ≤ e)
    (hcount : count ≤ 32) (hmodulusPos : 0 < modulus)
    (haccReduced : acc < modulus)
    (hacc : Limbs.Represents s.memory 2048 count acc)
    (hbase : Limbs.Represents s.memory 1024 count base)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    let progress := BigExponent.exponentByteProgress s accumulatorWord count b
      e m baseOff expOff rest steps
    Limbs.Represents progress.memory 2048 count
        (exponentValueAfter s modulus base expOff steps acc) ∧
      Limbs.Represents progress.memory 1024 count base ∧
      Limbs.Represents progress.memory 0 count modulus := by
  induction steps with
  | zero => exact ⟨hacc, hbase, hmodulus⟩
  | succ steps ih =>
      let before := BigExponent.exponentByteProgress s accumulatorWord count b
        e m baseOff expOff rest steps
      let beforeValue := exponentValueAfter s modulus base expOff steps acc
      let offset := UInt256.ofNat (expOff + steps)
      let byte := loadedExponentByte before expOff steps
      have hbefore := ih (by omega)
      have hbeforeReduced : beforeValue < modulus :=
        exponentValueAfter_lt s modulus base expOff steps acc hmodulusPos
          haccReduced
      have hbyteEnv : before.executionEnv = s.executionEnv := by
        exact BigExponent.exponentByteProgress_executionEnv s accumulatorWord
          count b e m baseOff expOff steps rest
      have hbyte : byte = loadedExponentByte s expOff steps := by
        simp only [byte, loadedExponentByte]
        rw [hbyteEnv]
      have hbits := exponentBitProgress_represents before accumulatorWord count
        b e m baseOff expOff steps offset byte rest 8 beforeValue base modulus
        (by omega) hcount hmodulusPos hbeforeReduced hbefore.1 hbefore.2.1
        hbefore.2.2
      have hbyteLt : byte.toNat < 256 := by
        rw [hbyte]
        exact loadedExponentByte_lt s expOff steps
      have hstepEq := natBitAfter_eight_eq_natExpStep modulus byte beforeValue
        base hbeforeReduced hbyteLt
      rw [hstepEq] at hbits
      simpa [BigExponent.exponentByteProgress, before, beforeValue, offset,
        byte, exponentValueAfter, hbyte] using hbits

theorem loadedExponentByte_header (input : ByteArray) (i : Nat)
    (hoff : Word.expOffset input + i < 2 ^ 256) :
    loadedExponentByte (Main.headerState input) (Word.expOffset input) i =
      WordCorrect.exponentByte input i := by
  unfold loadedExponentByte WordCorrect.exponentByte Word.byteWord
    Accessors.calldataByteValue
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff]
  rfl

theorem exponentValueAfter_executionEnv (s t : State)
    (modulus base expOff steps acc : Nat) (henv : s.executionEnv = t.executionEnv) :
    exponentValueAfter s modulus base expOff steps acc =
      exponentValueAfter t modulus base expOff steps acc := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      have hbyte : loadedExponentByte s expOff steps =
          loadedExponentByte t expOff steps := by
        unfold loadedExponentByte
        rw [henv]
      rw [exponentValueAfter, exponentValueAfter, ih, hbyte]

theorem exponentValueAfter_header_eq_natExpAfter (input : ByteArray)
    (modulus base steps acc : Nat)
    (hoff : Word.expOffset input + steps < 2 ^ 256) :
    exponentValueAfter (Main.headerState input) modulus base
        (Word.expOffset input) steps acc =
      WordCorrect.natExpAfter input modulus base steps acc := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [exponentValueAfter, WordCorrect.natExpAfter, ih (by omega),
        loadedExponentByte_header input steps (by omega)]

theorem exponentValueAfter_header_eq (input : ByteArray)
    (modulus base acc : Nat) (hvalid : ValidInput input)
    (hacc : acc < modulus) :
    exponentValueAfter (Main.headerState input) modulus base
        (Word.expOffset input) (exponentSize input) acc =
      (acc ^ (256 ^ exponentSize input) *
        base ^ (Precompile.bytesToNatPadded input (Word.expOffset input)
          (exponentSize input))) % modulus := by
  have hoff : Word.expOffset input + exponentSize input < 2 ^ 256 := by
    rcases hvalid with ⟨_, hb, he, _⟩
    simp only [Word.expOffset]
    omega
  rw [exponentValueAfter_header_eq_natExpAfter input modulus base
    (exponentSize input) acc hoff]
  exact WordCorrect.natExpAfter_eq input modulus base acc
    (exponentSize input) hvalid (by omega) hacc

end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentCorrect
