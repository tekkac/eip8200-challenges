import Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentCorrect
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
/-! # Functional correctness of multi-limb base conversion -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigBaseCorrect

open EvmSemantics
open EvmSemantics.EVM

open BigBase

theorem baseBit_toNat_le_one (byte : UInt256) (j : Nat) :
    (baseBit byte j).toNat ≤ 1 := by
  rw [baseBit, Challenge.EvmProof.Word.word_toNat_land,
    show (1 : UInt256).toNat = 1 by decide]
  exact Nat.and_le_right

theorem baseBit_toNat_eq (byte : UInt256) (j : Nat) (hj : j < 8) :
    (baseBit byte j).toNat = WordCorrect.exponentBitNat byte j := by
  have hsame : baseBit byte j = BigExponent.exponentBit byte j := by rfl
  rw [hsame]
  exact BigExponentCorrect.exponentBit_toNat_eq byte j hj

def baseBitStep (modulus : Nat) (byte : UInt256) (j acc : Nat) : Nat :=
  (2 * acc + (baseBit byte j).toNat) % modulus

def baseBitAfter (modulus : Nat) (byte : UInt256) : Nat → Nat → Nat
  | 0, acc => acc
  | j + 1, acc => baseBitStep modulus byte j
      (baseBitAfter modulus byte j acc)

theorem baseBitStep_lt (modulus : Nat) (byte : UInt256) (j acc : Nat)
    (hmodulusPos : 0 < modulus) : baseBitStep modulus byte j acc < modulus :=
  Nat.mod_lt _ hmodulusPos

theorem baseBitAfter_lt (modulus : Nat) (byte : UInt256) (steps acc : Nat)
    (hmodulusPos : 0 < modulus) (hacc : acc < modulus) :
    baseBitAfter modulus byte steps acc < modulus := by
  induction steps with
  | zero => exact hacc
  | succ steps ih => exact baseBitStep_lt modulus byte steps _ hmodulusPos

theorem bitProgress_represents (s : State) (count : Nat) (byte : UInt256)
    (steps acc modulus : Nat) (hsteps : steps ≤ 8) (hcount : count ≤ 32)
    (hmodulusPos : 0 < modulus) (haccReduced : acc < modulus)
    (hacc : Limbs.Represents s.memory 1024 count acc)
    (hone : Limbs.Represents s.memory 3072 count 1)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    let progress := bitProgress count byte steps s
    Limbs.Represents progress.memory 1024 count
        (baseBitAfter modulus byte steps acc) ∧
      Limbs.Represents progress.memory 3072 count 1 ∧
      Limbs.Represents progress.memory 0 count modulus := by
  induction steps with
  | zero => exact ⟨hacc, hone, hmodulus⟩
  | succ steps ih =>
      let before := bitProgress count byte steps s
      let beforeValue := baseBitAfter modulus byte steps acc
      let doubled := BigHelpers.addReturned before 1024 1024 1 0 count 875 []
      let bit := (baseBit byte steps).toNat
      have h0 : (0 : UInt256) = UInt256.ofNat 0 := by decide
      have h1 : (1 : UInt256) = UInt256.ofNat 1 := by decide
      have h1024 : (1024 : UInt256) = UInt256.ofNat 1024 := by decide
      have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
      have h875 : (875 : UInt256) = UInt256.ofNat 875 := by decide
      have h900 : (900 : UInt256) = UInt256.ofNat 900 := by decide
      have hbefore := ih (by omega)
      have hbeforeReduced : beforeValue < modulus :=
        baseBitAfter_lt modulus byte steps acc hmodulusPos haccReduced
      have hdoubled : Limbs.Represents doubled.memory 1024 count
          ((beforeValue + beforeValue) % modulus) := by
        simpa [doubled, h0, h1, h1024, h875] using
          BigHelpers.addReturned_represents_mod before 1024 1024 0 count 1
            beforeValue beforeValue modulus 875 [] (by omega) (by omega)
            (by omega) (by omega) (by omega) (Or.inl rfl) (Or.inr (by omega))
            (Or.inl (by omega)) (Or.inl (by omega)) hbefore.1 hbefore.1
            hbefore.2.2 hbeforeReduced hbeforeReduced.le hbefore.2.2.1
      have hdoubledOne : Limbs.Represents doubled.memory 3072 count 1 := by
        simpa [doubled, h0, h1, h1024, h875] using
          BigHelpers.addReturned_preserves_region before 1024 1024 1 0 3072
            count 1 875 [] (by omega) (by omega) (Or.inl (by omega))
            (Or.inl (by omega)) hbefore.2.1
      have hdoubledModulus : Limbs.Represents doubled.memory 0 count modulus := by
        simpa [doubled, h0, h1, h1024, h875] using
          BigHelpers.addReturned_preserves_region before 1024 1024 1 0 0
            count modulus 875 [] (by omega) (by omega) (Or.inr (by omega))
            (Or.inl (by omega)) hbefore.2.2
      have hdoubleReduced : (beforeValue + beforeValue) % modulus < modulus :=
        Nat.mod_lt _ hmodulusPos
      have hbitLe : bit ≤ 1 := baseBit_toNat_le_one byte steps
      let after := BigHelpers.addReturned doubled 1024 3072
        (baseBit byte steps) 0 count 900 []
      have hbitWord : baseBit byte steps = UInt256.ofNat bit :=
        Challenge.EvmProof.Word.word_eq_ofNat_toNat _
      have hafterEq : after = BigHelpers.addReturned doubled
          (UInt256.ofNat 1024) (UInt256.ofNat 3072) (UInt256.ofNat bit)
          (UInt256.ofNat 0) count (UInt256.ofNat 900) [] := by
        simp only [after]
        rw [hbitWord, h0, h1024, h3072, h900]
      have hafter : Limbs.Represents after.memory 1024 count
          ((((beforeValue + beforeValue) % modulus) + bit) % modulus) := by
        rw [hafterEq]
        simpa only [Nat.mul_one] using
          BigHelpers.addReturned_represents_mod doubled 1024 3072 0 count bit
            ((beforeValue + beforeValue) % modulus) 1 modulus
            (UInt256.ofNat 900) [] hbitLe
            (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
            (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
            hdoubled hdoubledOne hdoubledModulus hdoubleReduced
            (by omega) hdoubledModulus.1
      have hafterOne : Limbs.Represents after.memory 3072 count 1 := by
        rw [hafterEq]
        exact
          BigHelpers.addReturned_preserves_region doubled 1024 3072 bit 0 3072
            count 1 (UInt256.ofNat 900) [] (by omega) (by omega)
            (Or.inl (by omega))
            (Or.inl (by omega)) hdoubledOne
      have hafterModulus : Limbs.Represents after.memory 0 count modulus := by
        rw [hafterEq]
        exact
          BigHelpers.addReturned_preserves_region doubled 1024 3072 bit 0 0
            count modulus (UInt256.ofNat 900) [] (by omega) (by omega)
            (Or.inr (by omega))
            (Or.inl (by omega)) hdoubledModulus
      have hvalue :
          (((beforeValue + beforeValue) % modulus) + bit) % modulus =
            baseBitStep modulus byte steps beforeValue := by
        calc
          (((beforeValue + beforeValue) % modulus) + bit) % modulus =
              ((beforeValue + beforeValue) + bit) % modulus :=
            Nat.mod_add_mod _ _ _
          _ = baseBitStep modulus byte steps beforeValue := by
            simp only [baseBitStep, bit]
            congr 2
            omega
      rw [hvalue] at hafter
      simpa [bitProgress, before, doubled, after, beforeValue,
        baseBitAfter] using ⟨hafter, hafterOne, hafterModulus⟩

theorem bitProgress_preserves_2048 (s : State) (count : Nat)
    (byte : UInt256) (steps value : Nat) (hsteps : steps ≤ 8)
    (hcount : count ≤ 32)
    (hrep : Limbs.Represents s.memory 2048 count value) :
    Limbs.Represents (bitProgress count byte steps s).memory 2048 count value := by
  induction steps with
  | zero => exact hrep
  | succ steps ih =>
      let before := bitProgress count byte steps s
      let doubled := BigHelpers.addReturned before 1024 1024 1 0 count 875 []
      let bit := (baseBit byte steps).toNat
      let after := BigHelpers.addReturned doubled 1024 3072
        (baseBit byte steps) 0 count 900 []
      have hbefore := ih (by omega)
      have h0 : (0 : UInt256) = UInt256.ofNat 0 := by decide
      have h1 : (1 : UInt256) = UInt256.ofNat 1 := by decide
      have h1024 : (1024 : UInt256) = UInt256.ofNat 1024 := by decide
      have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
      have h875 : (875 : UInt256) = UInt256.ofNat 875 := by decide
      have h900 : (900 : UInt256) = UInt256.ofNat 900 := by decide
      have hdoubled : Limbs.Represents doubled.memory 2048 count value := by
        simpa [doubled, h0, h1, h1024, h875] using
          BigHelpers.addReturned_preserves_region before 1024 1024 1 0 2048
            count value (UInt256.ofNat 875) [] (by omega) (by omega)
            (Or.inl (by omega)) (Or.inl (by omega)) hbefore
      have hbitWord : baseBit byte steps = UInt256.ofNat bit :=
        Challenge.EvmProof.Word.word_eq_ofNat_toNat _
      have hafterEq : after = BigHelpers.addReturned doubled
          (UInt256.ofNat 1024) (UInt256.ofNat 3072) (UInt256.ofNat bit)
          (UInt256.ofNat 0) count (UInt256.ofNat 900) [] := by
        simp only [after]
        rw [hbitWord, h0, h1024, h3072, h900]
      have hafter : Limbs.Represents after.memory 2048 count value := by
        rw [hafterEq]
        exact BigHelpers.addReturned_preserves_region doubled 1024 3072
          bit 0 2048 count value (UInt256.ofNat 900) [] (by omega) (by omega)
          (Or.inl (by omega)) (Or.inl (by omega)) hdoubled
      simpa [bitProgress, before, doubled, after] using hafter

theorem baseBitAfter_eq (modulus : Nat) (byte : UInt256) (steps acc : Nat)
    (hsteps : steps ≤ 8) (hacc : acc < modulus) :
    baseBitAfter modulus byte steps acc =
      (acc * 2 ^ steps + WordCorrect.bitPrefix byte steps) % modulus := by
  induction steps with
  | zero => simp [baseBitAfter, WordCorrect.bitPrefix, Nat.mod_eq_of_lt hacc]
  | succ steps ih =>
      let value := acc * 2 ^ steps + WordCorrect.bitPrefix byte steps
      let bit := (baseBit byte steps).toNat
      have hbit : bit = WordCorrect.exponentBitNat byte steps :=
        baseBit_toNat_eq byte steps (by omega)
      have hmul : (2 * (value % modulus)) % modulus =
          (2 * value) % modulus := by
        calc
          (2 * (value % modulus)) % modulus =
              (2 % modulus * ((value % modulus) % modulus)) % modulus :=
            Nat.mul_mod _ _ _
          _ = (2 % modulus * (value % modulus)) % modulus := by
            rw [Nat.mod_mod]
          _ = (2 * value) % modulus := (Nat.mul_mod _ _ _).symm
      rw [baseBitAfter, baseBitStep, ih (by omega)]
      calc
        (2 * (value % modulus) + bit) % modulus =
            ((2 * (value % modulus)) % modulus + bit) % modulus := by
          rw [Nat.mod_add_mod]
        _ = ((2 * value) % modulus + bit) % modulus := by rw [hmul]
        _ = (2 * value + bit) % modulus := Nat.mod_add_mod _ _ _
        _ = (acc * 2 ^ (steps + 1) +
              WordCorrect.bitPrefix byte (steps + 1)) % modulus := by
          simp only [value, bit, WordCorrect.bitPrefix, hbit, pow_succ]
          congr 1
          ring

theorem baseBitAfter_eight (modulus : Nat) (byte : UInt256) (acc : Nat)
    (hacc : acc < modulus) (hbyte : byte.toNat < 256) :
    baseBitAfter modulus byte 8 acc =
      (acc * 256 + byte.toNat) % modulus := by
  rw [baseBitAfter_eq modulus byte 8 acc (by omega) hacc,
    WordCorrect.bitPrefix_eight byte hbyte]
  norm_num

theorem loadedBaseByte_lt (s : State) (baseOff i : Nat) :
    (loadedBaseByte s baseOff i).toNat < 256 := by
  change (BigExponent.loadedExponentByte s baseOff i).toNat < 256
  exact BigExponentCorrect.loadedExponentByte_lt s baseOff i

def baseValueAfter (s : State) (modulus baseOff : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 =>
      (baseValueAfter s modulus baseOff i * 256 +
        (loadedBaseByte s baseOff i).toNat) % modulus

theorem baseValueAfter_lt (s : State) (modulus baseOff steps : Nat)
    (hmodulusPos : 0 < modulus) :
    baseValueAfter s modulus baseOff steps < modulus := by
  cases steps with
  | zero => simpa [baseValueAfter] using hmodulusPos
  | succ steps =>
      rw [baseValueAfter]
      exact Nat.mod_lt _ hmodulusPos

theorem baseProgress_represents (s : State) (count baseOff steps modulus : Nat)
    (hcount : count ≤ 32) (hmodulusPos : 0 < modulus)
    (hzero : Limbs.Represents s.memory 1024 count 0)
    (hone : Limbs.Represents s.memory 3072 count 1)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    let progress := baseProgress count baseOff steps s
    Limbs.Represents progress.memory 1024 count
        (baseValueAfter s modulus baseOff steps) ∧
      Limbs.Represents progress.memory 3072 count 1 ∧
      Limbs.Represents progress.memory 0 count modulus := by
  induction steps with
  | zero => exact ⟨hzero, hone, hmodulus⟩
  | succ steps ih =>
      let before := baseProgress count baseOff steps s
      let beforeValue := baseValueAfter s modulus baseOff steps
      let byte := loadedBaseByte before baseOff steps
      have hbefore := ih
      have hbeforeReduced : beforeValue < modulus :=
        baseValueAfter_lt s modulus baseOff steps hmodulusPos
      have hbyte : byte = loadedBaseByte s baseOff steps := by
        exact BigBase.loadedBaseByte_baseProgress count baseOff steps steps s
      have hbits := bitProgress_represents before count byte 8 beforeValue
        modulus (by omega) hcount hmodulusPos hbeforeReduced hbefore.1
        hbefore.2.1 hbefore.2.2
      have hbyteLt : byte.toNat < 256 := by
        rw [hbyte]
        exact loadedBaseByte_lt s baseOff steps
      have heq := baseBitAfter_eight modulus byte beforeValue hbeforeReduced
        hbyteLt
      rw [heq] at hbits
      simpa [baseProgress, baseValueAfter, before, beforeValue, byte, hbyte]
        using hbits

theorem baseProgress_preserves_2048 (s : State) (count baseOff steps value : Nat)
    (hcount : count ≤ 32)
    (hrep : Limbs.Represents s.memory 2048 count value) :
    Limbs.Represents (baseProgress count baseOff steps s).memory 2048 count
      value := by
  induction steps with
  | zero => exact hrep
  | succ steps ih =>
      let before := baseProgress count baseOff steps s
      let byte := loadedBaseByte before baseOff steps
      have hbits := bitProgress_preserves_2048 before count byte 8 value
        (by omega) hcount ih
      simpa [baseProgress, before, byte] using hbits

theorem loadedBaseByte_header_toNat (input : ByteArray) (baseOff i : Nat)
    (_hfit : baseOff + i < 2 ^ 256) :
    (loadedBaseByte (Main.headerState input) baseOff i).toNat =
      (YulSemantics.EVM.byteFrom input.toList (baseOff + i)).toNat := by
  have h := congrArg UInt256.toNat
    (Challenge.EvmProof.Bytes.byteAt_zero_readWord input (baseOff + i))
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt
      ((YulSemantics.EVM.byteFrom input.toList (baseOff + i)).toNat_lt.trans
        (by norm_num : 256 < 2 ^ 256))] at h
  change (UInt256.byteAt ⟨0⟩
    (MachineState.readWord input (baseOff + i))).toNat = _
  exact h

theorem baseValueAfter_header_eq (input : ByteArray) (modulus steps : Nat)
    (hfit : 96 + steps < 2 ^ 256) :
    baseValueAfter (Main.headerState input) modulus 96 steps =
      Precompile.bytesToNatPadded input 96 steps % modulus := by
  induction steps with
  | zero => simp [baseValueAfter,
      Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width]
  | succ steps ih =>
      rw [baseValueAfter, ih (by omega),
        loadedBaseByte_header_toNat input 96 steps (by omega),
        Challenge.EvmProof.Bytes.bytesToNatPadded_succ]
      simp [Nat.add_mod, Nat.mul_mod]

theorem represents_writeWord_disjoint_region (memory : ByteArray)
    (dst ptr count value word : Nat)
    (hdisjoint : dst + 32 ≤ ptr ∨ ptr + 32 * count ≤ dst)
    (hrep : Limbs.Represents memory ptr count value) :
    Limbs.Represents
      (MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word 32) dst)
      ptr count value := by
  refine ⟨hrep.1, ?_⟩
  rw [← hrep.2]
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro j hj
  have hj' : j < count := by simpa using hj
  apply congrArg UInt256.toNat
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  rcases hdisjoint with hbefore | hafter
  · right
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
    omega
  · left
    omega

theorem loadMemory_preserves_region (calldata : ByteArray) (memory : ByteArray)
    (offset dst length iter ptr count value : Nat) (hiter : iter ≤ length)
    (hlength : length < 2 ^ 256)
    (hdstFit : dst + 32 * Limbs.limbCount length < 2 ^ 256)
    (hbefore : dst + 32 * Limbs.limbCount length ≤ ptr)
    (hrep : Limbs.Represents memory ptr count value) :
    Limbs.Represents
      (BigLoad.loadMemory calldata offset (UInt256.ofNat dst) length iter memory)
      ptr count value := by
  induction iter with
  | zero => exact hrep
  | succ iter ih =>
      let before := BigLoad.loadMemory calldata offset (UInt256.ofNat dst)
        length iter memory
      let addr := BigLoad.loadAt (UInt256.ofNat dst) length iter
      let shifted := UInt256.shiftLeft (BigLoad.loadByte calldata offset iter)
        (BigLoad.loadShiftWord (UInt256.ofNat length) iter)
      let word := UInt256.lor (MachineState.readWord before addr.toNat) shifted
      have haddr := BigLoadCorrect.loadAt_ofNat dst length iter hlength
        (by omega) hdstFit
      have haddrBefore : addr.toNat + 32 ≤ ptr := by
        rw [haddr]
        have hlimb : BigLoad.loadLimb length iter < Limbs.limbCount length := by
          unfold BigLoad.loadLimb BigLoad.loadReverse Limbs.limbCount
          omega
        omega
      simpa [BigLoad.loadMemory, before, addr, shifted, word] using
        represents_writeWord_disjoint_region before addr.toNat ptr count value
          word.toNat (Or.inl haddrBefore) (ih (by omega))

theorem setupReturned_base_buffers_zero (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hmBound : m ≤ 1024)
    (hmodOff : modOff < 2 ^ 256) :
    let returned := BigSetup.setupReturned s b e m baseOff expOff modOff
      returnDest rest
    let n := Limbs.limbCount m
    Limbs.Represents returned.memory 1024 n 0 ∧
      Limbs.Represents returned.memory 2048 n 0 := by
  let n := Limbs.limbCount m
  let s0 := BigSetup.afterClear0 s b e m baseOff expOff modOff returnDest rest
  let s1 := BigSetup.afterClear1024 s b e m baseOff expOff modOff returnDest rest
  let s2 := BigSetup.afterClear2048 s b e m baseOff expOff modOff returnDest rest
  let s3 := BigSetup.afterClear6144 s b e m baseOff expOff modOff returnDest rest
  have hn : n ≤ 32 := Limbs.limbCount_le_32 m hmBound
  have hm : m < 2 ^ 256 := by omega
  have h0 : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have h1024 : (1024 : UInt256) = UInt256.ofNat 1024 := by decide
  have h2048 : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
  have h6144 : (6144 : UInt256) = UInt256.ofNat 6144 := by decide
  have hmNat : (UInt256.ofNat m).toNat = m := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hm]
  have hmodOffNat : (UInt256.ofNat modOff).toNat = modOff := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hmodOff]
  have hz1024s1 : Limbs.Represents s1.memory 1024 n 0 := by
    simpa [s1, BigSetup.afterClear1024, BigHelpers.clearReturned, h1024]
      using BigHelpers.clearMemory_represents_zero s0.memory 1024 n (by omega)
  have hz1024s2 : Limbs.Represents s2.memory 1024 n 0 := by
    simpa [s2, BigSetup.afterClear2048, BigHelpers.clearReturned, h2048] using
      BigHelpers.represents_clearMemory_disjoint_region s1.memory 2048 1024 n
        0 (by omega) (Or.inr (by omega)) hz1024s1
  have hz1024s3 : Limbs.Represents s3.memory 1024 n 0 := by
    simpa [s3, BigSetup.afterClear6144, BigHelpers.clearReturned, h6144] using
      BigHelpers.represents_clearMemory_disjoint_region s2.memory 6144 1024 n
        0 (by omega) (Or.inr (by omega)) hz1024s2
  have hz2048s2 : Limbs.Represents s2.memory 2048 n 0 := by
    simpa [s2, BigSetup.afterClear2048, BigHelpers.clearReturned, h2048]
      using BigHelpers.clearMemory_represents_zero s1.memory 2048 n (by omega)
  have hz2048s3 : Limbs.Represents s3.memory 2048 n 0 := by
    simpa [s3, BigSetup.afterClear6144, BigHelpers.clearReturned, h6144] using
      BigHelpers.represents_clearMemory_disjoint_region s2.memory 6144 2048 n
        0 (by omega) (Or.inr (by omega)) hz2048s2
  have hz1024 := loadMemory_preserves_region s3.executionEnv.calldata
    s3.memory modOff 0 m m 1024 n 0 (by omega) hm (by omega) (by omega)
    hz1024s3
  have hz2048 := loadMemory_preserves_region s3.executionEnv.calldata
    s3.memory modOff 0 m m 2048 n 0 (by omega) hm (by omega) (by omega)
    hz2048s3
  exact ⟨by
    simpa [BigSetup.setupReturned, s3, BigLoad.loadReturned,
      BigLoad.loadLoop, h0, hmNat, hmodOffNat, n] using hz1024,
    by simpa [BigSetup.setupReturned, s3, BigLoad.loadReturned,
      BigLoad.loadLoop, h0, hmNat, hmodOffNat, n] using hz2048⟩

theorem baseLoopEntry_initial (s : State) (accumulator : UInt256)
    (count modulusValue : Nat) (rest : List UInt256) (hcountPos : 0 < count)
    (hcount : count ≤ 32)
    (hzero : Limbs.Represents s.memory 1024 count 0)
    (hzero2048 : Limbs.Represents s.memory 2048 count 0)
    (hmodulus : Limbs.Represents s.memory 0 count modulusValue) :
    let entry := BigBase.baseLoopEntry s accumulator count rest
    Limbs.Represents entry.memory 1024 count 0 ∧
      Limbs.Represents entry.memory 3072 count 1 ∧
      Limbs.Represents entry.memory 2048 count 0 ∧
      Limbs.Represents entry.memory 0 count modulusValue := by
  let scanned := BigModulus.scanNonzero s count rest
  let cleared := BigBase.afterClearDouble s accumulator count rest
  let written := MachineState.writeBytes cleared.memory
    (Data.Bytes.natToBytesPadded 1 32) 3072
  have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
  have hscannedZero : Limbs.Represents scanned.memory 1024 count 0 := by
    simpa [scanned, BigModulus.scanNonzero] using hzero
  have hscannedModulus : Limbs.Represents scanned.memory 0 count modulusValue := by
    simpa [scanned, BigModulus.scanNonzero] using hmodulus
  have hscannedZero2048 : Limbs.Represents scanned.memory 2048 count 0 := by
    simpa [scanned, BigModulus.scanNonzero] using hzero2048
  have hcleared3072 : Limbs.Represents cleared.memory 3072 count 0 := by
    simpa [cleared, BigBase.afterClearDouble, BigHelpers.clearReturned,
      scanned, h3072] using
      BigHelpers.clearMemory_represents_zero scanned.memory 3072 count
        (by omega)
  have hclearedZero : Limbs.Represents cleared.memory 1024 count 0 := by
    simpa [cleared, BigBase.afterClearDouble, BigHelpers.clearReturned,
      scanned, h3072] using
      BigHelpers.represents_clearMemory_disjoint_region scanned.memory 3072
        1024 count 0 (by omega) (Or.inr (by omega)) hscannedZero
  have hclearedModulus : Limbs.Represents cleared.memory 0 count modulusValue := by
    simpa [cleared, BigBase.afterClearDouble, BigHelpers.clearReturned,
      scanned, h3072] using
      BigHelpers.represents_clearMemory_disjoint_region scanned.memory 3072 0
        count modulusValue (by omega) (Or.inr (by omega)) hscannedModulus
  have hclearedZero2048 : Limbs.Represents cleared.memory 2048 count 0 := by
    simpa [cleared, BigBase.afterClearDouble, BigHelpers.clearReturned,
      scanned, h3072] using
      BigHelpers.represents_clearMemory_disjoint_region scanned.memory 3072
        2048 count 0 (by omega) (Or.inr (by omega)) hscannedZero2048
  have hreadZero :
      (MachineState.readWord cleared.memory (3072 + 32 * 0)).toNat = 0 := by
    simpa [cleared, BigBase.afterClearDouble, BigHelpers.clearReturned,
      scanned, h3072] using
      BigHelpers.readWord_clearMemory scanned.memory 3072 count 0 (by omega)
        (by omega)
  have hvalue := BigLoadCorrect.value_memoryLimbs_write_add cleared.memory 3072 count
    0 1 hcountPos (by rw [hreadZero]; norm_num)
  have hclearedValue := Limbs.value_of_represents hcleared3072
  rw [hclearedValue, Nat.zero_add, Nat.pow_zero, Nat.mul_one] at hvalue
  have hwrittenOne : Limbs.Represents written 3072 count 1 := by
    apply (Limbs.represents_iff_value (by
      exact Nat.one_lt_pow (by omega) Limbs.radix_gt_one)).2
    simpa [written, hreadZero] using hvalue
  have hwrittenZero : Limbs.Represents written 1024 count 0 := by
    exact represents_writeWord_disjoint_region cleared.memory 3072 1024 count
      0 1 (Or.inr (by omega)) hclearedZero
  have hwrittenModulus : Limbs.Represents written 0 count modulusValue := by
    exact represents_writeWord_disjoint_region cleared.memory 3072 0 count
      modulusValue 1 (Or.inr (by omega)) hclearedModulus
  have hwrittenZero2048 : Limbs.Represents written 2048 count 0 := by
    exact represents_writeWord_disjoint_region cleared.memory 3072 2048 count
      0 1 (Or.inr (by omega)) hclearedZero2048
  exact ⟨by simpa [BigBase.baseLoopEntry, written, cleared] using hwrittenZero,
    by simpa [BigBase.baseLoopEntry, written, cleared] using hwrittenOne,
    by simpa [BigBase.baseLoopEntry, written, cleared] using hwrittenZero2048,
    by simpa [BigBase.baseLoopEntry, written, cleared] using
      hwrittenModulus⟩

theorem baseValueAfter_executionEnv (s t : State)
    (modulus baseOff steps : Nat) (henv : s.executionEnv = t.executionEnv) :
    baseValueAfter s modulus baseOff steps =
      baseValueAfter t modulus baseOff steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      have hbyte : loadedBaseByte s baseOff steps =
          loadedBaseByte t baseOff steps := by
        unfold loadedBaseByte
        rw [henv]
      rw [baseValueAfter, baseValueAfter, ih, hbyte]

theorem initialAccumulator_represents (s : State) (accumulator : UInt256)
    (count baseSize e m baseOff : Nat) (rest : List UInt256)
    (modulusValue : Nat) (hcountPos : 0 < count) (hcount : count ≤ 32)
    (hmodulusPos : 0 < modulusValue)
    (hzero : Limbs.Represents s.memory 1024 count 0)
    (hone : Limbs.Represents s.memory 3072 count 1)
    (hzero2048 : Limbs.Represents s.memory 2048 count 0)
    (hmodulus : Limbs.Represents s.memory 0 count modulusValue) :
    let returned := BigBaseLoop.initialAccumulator s accumulator count baseSize
      e m baseOff rest
    Limbs.Represents returned.memory 2048 count (1 % modulusValue) ∧
      Limbs.Represents returned.memory 1024 count
        (baseValueAfter s modulusValue baseOff baseSize) ∧
      Limbs.Represents returned.memory 0 count modulusValue := by
  let progress := baseProgress count baseOff baseSize s
  let baseValue := baseValueAfter s modulusValue baseOff baseSize
  let exit := BigBaseLoop.baseConvertedExit s accumulator count baseSize e m
    baseOff rest
  let helperRest := [accumulator, UInt256.ofNat count,
    UInt256.ofNat baseSize] ++ [UInt256.ofNat e, UInt256.ofNat m,
      UInt256.ofNat baseOff] ++ rest
  have h0 : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have h1 : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h2048 : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
  have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
  have h944 : (944 : UInt256) = UInt256.ofNat 944 := by decide
  have hprogress := baseProgress_represents s count baseOff baseSize
    modulusValue hcount hmodulusPos hzero hone hmodulus
  have hprogressZero := baseProgress_preserves_2048 s count baseOff baseSize 0
    hcount hzero2048
  have hexitBase : Limbs.Represents exit.memory 1024 count baseValue := by
    simpa [exit, BigBaseLoop.baseConvertedExit, BigBase.outerExit,
      BigBase.outerLoop, progress, baseValue] using hprogress.1
  have hexitOne : Limbs.Represents exit.memory 3072 count 1 := by
    simpa [exit, BigBaseLoop.baseConvertedExit, BigBase.outerExit,
      BigBase.outerLoop, progress] using hprogress.2.1
  have hexitZero : Limbs.Represents exit.memory 2048 count 0 := by
    simpa [exit, BigBaseLoop.baseConvertedExit, BigBase.outerExit,
      BigBase.outerLoop, progress] using hprogressZero
  have hexitModulus : Limbs.Represents exit.memory 0 count modulusValue := by
    simpa [exit, BigBaseLoop.baseConvertedExit, BigBase.outerExit,
      BigBase.outerLoop, progress] using hprogress.2.2
  have hacc : Limbs.Represents
      (BigBaseLoop.initialAccumulator s accumulator count baseSize e m baseOff
        rest).memory 2048 count (1 % modulusValue) := by
    simpa [BigBaseLoop.initialAccumulator, helperRest, exit, h0, h1, h2048,
      h3072, h944] using
      BigHelpers.addReturned_represents_mod exit 2048 3072 0 count 1 0 1
        modulusValue (UInt256.ofNat 944) helperRest (by omega) (by omega)
        (by omega) (by omega) (by omega) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
        hexitZero hexitOne hexitModulus (by omega) (by omega) hexitModulus.1
  have hbase : Limbs.Represents
      (BigBaseLoop.initialAccumulator s accumulator count baseSize e m baseOff
        rest).memory 1024 count baseValue := by
    simpa [BigBaseLoop.initialAccumulator, helperRest, exit, h0, h1, h2048,
      h3072, h944] using
      BigHelpers.addReturned_preserves_region exit 2048 3072 1 0 1024 count
        baseValue (UInt256.ofNat 944) helperRest (by omega) (by omega)
        (Or.inr (by omega)) (Or.inl (by omega)) hexitBase
  have hmod : Limbs.Represents
      (BigBaseLoop.initialAccumulator s accumulator count baseSize e m baseOff
        rest).memory 0 count modulusValue := by
    simpa [BigBaseLoop.initialAccumulator, helperRest, exit, h0, h1, h2048,
      h3072, h944] using
      BigHelpers.addReturned_preserves_region exit 2048 3072 1 0 0 count
        modulusValue (UInt256.ofNat 944) helperRest (by omega) (by omega)
        (Or.inr (by omega)) (Or.inl (by omega)) hexitModulus
  exact ⟨hacc, by simpa [baseValue] using hbase, hmod⟩

theorem exponentState_initial (input : ByteArray) (returnDest : UInt256)
    (rest : List UInt256) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input)
    (hmodulusPos : 0 < Word.modulusValue input) :
    let b := baseSize input
    let e := exponentSize input
    let m := modulusSize input
    let expOff := Word.expOffset input
    let modOff := Word.modulusOffset input
    let entry := BigComplete.exponentState (Main.headerState input) b e m 96
      expOff modOff returnDest rest
    Limbs.Represents entry.memory 2048 (Limbs.limbCount m)
        (1 % Word.modulusValue input) ∧
      Limbs.Represents entry.memory 1024 (Limbs.limbCount m)
        (WordCorrect.baseNat input % Word.modulusValue input) ∧
      Limbs.Represents entry.memory 0 (Limbs.limbCount m)
        (Word.modulusValue input) := by
  let b := baseSize input
  let e := exponentSize input
  let m := modulusSize input
  let expOff := Word.expOffset input
  let modOff := Word.modulusOffset input
  let n := Limbs.limbCount m
  let header := Main.headerState input
  let loaded := BigComplete.setupState header b e m 96 expOff modOff returnDest
    rest
  let scanTail := BigComplete.scanRest b e m 96 expOff modOff returnDest rest
  let accumulator := BigComplete.modulusOr header b e m 96 expOff modOff
    returnDest rest
  let base := BigComplete.baseState header b e m 96 expOff modOff returnDest
    rest
  let baseTail := BigComplete.baseRest expOff modOff returnDest rest
  have hb : b ≤ 1024 := by simpa [b] using hvalid.2.1
  have hm : m ≤ 1024 := by simpa [m] using hvalid.2.2.2
  have hn : n ≤ 32 := Limbs.limbCount_le_32 m hm
  have hnPos : 0 < n := Limbs.limbCount_pos (by simp [m]; omega)
  have hmodOff : modOff < 2 ^ 256 := by
    rcases hvalid with ⟨_, hb', he', _⟩
    simp only [modOff, Word.modulusOffset, Word.expOffset]
    omega
  have hmodulus : Limbs.Represents loaded.memory 0 n
      (Word.modulusValue input) := by
    have hraw := BigSetup.setupReturned_modulus_represents header b e m 96
      expOff modOff returnDest rest hm hmodOff
    rw [show header.executionEnv.calldata = input by rfl] at hraw
    simpa [loaded, BigComplete.setupState, header, b, e, m, n, expOff,
      modOff, Word.modulusValue, Word.modulusOffset] using hraw
  have hzeros := setupReturned_base_buffers_zero header b e m 96 expOff modOff
    returnDest rest hm hmodOff
  have hinitial := baseLoopEntry_initial loaded accumulator n
    (Word.modulusValue input) scanTail hnPos hn hzeros.1 hzeros.2 hmodulus
  have hbaseZero : Limbs.Represents base.memory 1024 n 0 := by
    simpa [base, BigComplete.baseState, BigComplete.limbCount, loaded,
      accumulator, scanTail, n] using
      hinitial.1
  have hbaseOne : Limbs.Represents base.memory 3072 n 1 := by
    simpa [base, BigComplete.baseState, BigComplete.limbCount, loaded,
      accumulator, scanTail, n] using
      hinitial.2.1
  have hbaseZero2048 : Limbs.Represents base.memory 2048 n 0 := by
    simpa [base, BigComplete.baseState, BigComplete.limbCount, loaded,
      accumulator, scanTail, n] using
      hinitial.2.2.1
  have hbaseModulus : Limbs.Represents base.memory 0 n
      (Word.modulusValue input) := by
    simpa [base, BigComplete.baseState, BigComplete.limbCount, loaded,
      accumulator, scanTail, n] using
      hinitial.2.2.2
  have hreturned := initialAccumulator_represents base accumulator n b e m 96
    baseTail (Word.modulusValue input) hnPos hn hmodulusPos hbaseZero hbaseOne
    hbaseZero2048 hbaseModulus
  have hbaseEnv : base.executionEnv = header.executionEnv := by
    rfl
  have hvalueEnv := baseValueAfter_executionEnv base header
    (Word.modulusValue input) 96 b hbaseEnv
  have hvalueHeader := baseValueAfter_header_eq input (Word.modulusValue input)
    b (by omega)
  have hvalue : baseValueAfter base (Word.modulusValue input) 96 b =
      WordCorrect.baseNat input % Word.modulusValue input := by
    rw [hvalueEnv, hvalueHeader]
    rfl
  rw [hvalue] at hreturned
  simpa [BigComplete.exponentState, BigComplete.limbCount, base, accumulator,
    n, b, e, m, expOff, modOff, baseTail, header] using hreturned

end Challenge.Modexp.Submission.Proofs.Bytecode.BigBaseCorrect
