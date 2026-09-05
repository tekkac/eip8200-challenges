import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P7
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P8
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P9
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P10
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P11
import Challenge.Modexp.Submission.Proofs.Fast.Csub
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# The `MONPRO` subroutine of the appended Montgomery path

`MONPRO` occupies instruction indices 1379..1599 (pc 1939..2466).  It is
entered with stack `[pa, pb, pc, ret]`, computes the CIOS Montgomery product
`a * b * R⁻¹ mod m` of the `n`-limb blocks at `pa` and `pb` into the CIOS
scratch area, and tail-calls `CSUB` at pc 2642 with stack `[pc, ret]`.

This module starts with the 512-bit multiply-accumulate identity that every
CIOS row step relies on.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Monpro

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

/-! ## Word arithmetic -/

theorem word_toNat_mul (a b : UInt256) :
    (a * b).toNat = a.toNat * b.toNat % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl

theorem word_toNat_lt' (a b : UInt256) :
    (UInt256.lt a b).toNat = if a.toNat < b.toNat then 1 else 0 :=
  Challenge.EvmProof.Word.word_toNat_lt a b

theorem word_lt_size (a : UInt256) : a.toNat < 2 ^ 256 := a.val.isLt

/-- The `PUSH32` immediate the 512-bit multiply uses as the `MULMOD` modulus. -/
def maxWord : UInt256 :=
  UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935

theorem maxWord_toNat : maxWord.toNat = 2 ^ 256 - 1 := by
  rw [maxWord, Challenge.EvmProof.Word.word_toNat_ofNat]
  norm_num

theorem word_toNat_mulMod_max (a b : UInt256) :
    (UInt256.mulMod a b maxWord).toNat = a.toNat * b.toNat % (2 ^ 256 - 1) := by
  have hne : maxWord.val.val ≠ 0 := by
    have : maxWord.toNat = 2 ^ 256 - 1 := maxWord_toNat
    change maxWord.toNat ≠ 0
    omega
  rw [UInt256.mulMod, if_neg hne, Challenge.EvmProof.Word.word_toNat_ofNat,
    maxWord_toNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le
    (Nat.mod_lt _ (by norm_num)) (by norm_num))

/-! ## The 512-bit product

`lo = mul x y`, `mm = mulmod x y (2^256-1)`, `hi = mm - (lo + lt mm lo)`
satisfies `hi * 2^256 + lo = x * y` over the naturals. -/

/-- The high word of the 512-bit product, exactly as the bytecode computes it. -/
def mulHi (x y : UInt256) : UInt256 :=
  UInt256.mulMod x y maxWord - (x * y + UInt256.lt (UInt256.mulMod x y maxWord) (x * y))

private theorem high_lt {K X Y : Nat} (hK : 2 ≤ K) (hX : X < K) (hY : Y < K) :
    X * Y / K < K - 1 := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 2 := ⟨K - 2, by omega⟩
  rw [Nat.div_lt_iff_lt_mul (by omega), show K' + 2 - 1 = K' + 1 from by omega]
  have h1 : X * Y ≤ (K' + 1) * (K' + 1) := Nat.mul_le_mul (by omega) (by omega)
  nlinarith

private theorem mulHi_core {K H L M : Nat} (hK : 2 ≤ K)
    (hH : H + 1 < K) (hL : L < K) (hM : M = (H + L) % (K - 1)) :
    (K + M - (L + (if M < L then 1 else 0)) % K) % K = H := by
  rcases Nat.lt_or_ge (H + L) (K - 1) with hcase | hcase
  · have hMv : M = H + L := by rw [hM]; exact Nat.mod_eq_of_lt hcase
    rw [if_neg (by omega), Nat.add_zero, Nat.mod_eq_of_lt hL,
      show K + M - L = H + K by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · have hMv : M = H + L - (K - 1) := by
      rw [hM, Nat.mod_eq_sub_mod hcase, Nat.mod_eq_of_lt (by omega)]
    rw [if_pos (by omega)]
    rcases Nat.lt_or_ge (L + 1) K with hsub | hsub
    · rw [Nat.mod_eq_of_lt hsub, show K + M - (L + 1) = H by omega,
        Nat.mod_eq_of_lt (by omega)]
    · have hLK : L + 1 = K := by omega
      rw [hLK, Nat.mod_self, Nat.sub_zero, Nat.add_mod_left,
        Nat.mod_eq_of_lt (show M < K by omega)]
      omega

theorem mulHi_toNat (x y : UInt256) :
    (mulHi x y).toNat = x.toNat * y.toNat / 2 ^ 256 := by
  have hXlt : x.toNat < 2 ^ 256 := word_lt_size x
  have hYlt : y.toNat < 2 ^ 256 := word_lt_size y
  have hHlt : x.toNat * y.toNat / 2 ^ 256 < 2 ^ 256 - 1 :=
    high_lt (by norm_num) hXlt hYlt
  have hdm : 2 ^ 256 * (x.toNat * y.toNat / 2 ^ 256) + x.toNat * y.toNat % 2 ^ 256
      = x.toNat * y.toNat := Nat.div_add_mod _ _
  have hmodeq : (2 : Nat) ^ 256 ≡ 1 [MOD 2 ^ 256 - 1] := by
    unfold Nat.ModEq
    norm_num
  have hstep := (hmodeq.mul_right (x.toNat * y.toNat / 2 ^ 256)).add_right
    (x.toNat * y.toNat % 2 ^ 256)
  rw [Nat.one_mul, hdm] at hstep
  rw [mulHi, Challenge.EvmProof.Word.word_toNat_sub,
    Challenge.EvmProof.Word.word_toNat_add, word_toNat_mulMod_max,
    word_toNat_mul, word_toNat_lt', word_toNat_mulMod_max, word_toNat_mul]
  exact mulHi_core (K := 2 ^ 256) (by norm_num) (by omega)
    (Nat.mod_lt _ (by norm_num)) hstep

/-- The 512-bit product identity. -/
theorem mulHi_spec (x y : UInt256) :
    (mulHi x y).toNat * 2 ^ 256 + (x * y).toNat = x.toNat * y.toNat := by
  rw [mulHi_toNat, word_toNat_mul, Nat.mul_comm]
  exact Nat.div_add_mod _ _

/-! ## The multiply-accumulate step

Both CIOS limb loops execute the same instruction sequence: read the source
limb `x`, form the 512-bit product with the row multiplier `y`, add the
current `t` limb and the running carry, store the low word back and keep the
high word as the new carry. -/

/-- The stored limb of one multiply-accumulate step. -/
def macSum (x y t c : UInt256) : UInt256 := c + (t + x * y)

/-- The carry out of one multiply-accumulate step. -/
def macCarry (x y t c : UInt256) : UInt256 :=
  UInt256.lt (c + (t + x * y)) c + (UInt256.lt (t + x * y) t + mulHi x y)

private theorem carry_split (A B : Nat) (hA : A < 2 ^ 256) (hB : B < 2 ^ 256) :
    A + B = (if (A + B) % 2 ^ 256 < A then 1 else 0) * 2 ^ 256 + (A + B) % 2 ^ 256 := by
  rcases Nat.lt_or_ge (A + B) (2 ^ 256) with h | h
  · rw [Nat.mod_eq_of_lt h, if_neg (by omega)]
    omega
  · have hval : (A + B) % 2 ^ 256 = A + B - 2 ^ 256 := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [hval, if_pos (by omega)]
    omega

private theorem total_lt {K T X Y C : Nat} (hT : T < K) (hX : X < K) (hY : Y < K)
    (hC : C < K) : T + X * Y + C < K * K := by
  have h : X * Y ≤ (K - 1) * (K - 1) := Nat.mul_le_mul (by omega) (by omega)
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h
  nlinarith

/-- One multiply-accumulate step is exact over the naturals. -/
theorem macSpec (x y t c : UInt256) :
    (macCarry x y t c).toNat * 2 ^ 256 + (macSum x y t c).toNat =
      t.toNat + x.toNat * y.toNat + c.toNat := by
  have hx : x.toNat < 2 ^ 256 := word_lt_size x
  have hy : y.toNat < 2 ^ 256 := word_lt_size y
  have ht : t.toNat < 2 ^ 256 := word_lt_size t
  have hc : c.toNat < 2 ^ 256 := word_lt_size c
  have hprod := mulHi_spec x y
  have hlo : (x * y).toNat < 2 ^ 256 := word_lt_size (x * y)
  have hs1lt : (t + x * y).toNat < 2 ^ 256 := word_lt_size (t + x * y)
  have h1 : t.toNat + (x * y).toNat =
      (UInt256.lt (t + x * y) t).toNat * 2 ^ 256 + (t + x * y).toNat := by
    rw [word_toNat_lt', Challenge.EvmProof.Word.word_toNat_add t (x * y)]
    exact carry_split t.toNat (x * y).toNat ht hlo
  have h2 : c.toNat + (t + x * y).toNat =
      (UInt256.lt (c + (t + x * y)) c).toNat * 2 ^ 256 +
        (c + (t + x * y)).toNat := by
    rw [word_toNat_lt', Challenge.EvmProof.Word.word_toNat_add c (t + x * y)]
    exact carry_split c.toNat (t + x * y).toNat hc hs1lt
  have hkey : ((UInt256.lt (c + (t + x * y)) c).toNat +
        ((UInt256.lt (t + x * y) t).toNat + (mulHi x y).toNat)) * 2 ^ 256 +
        (c + (t + x * y)).toNat =
      t.toNat + x.toNat * y.toNat + c.toNat := by
    calc ((UInt256.lt (c + (t + x * y)) c).toNat +
            ((UInt256.lt (t + x * y) t).toNat + (mulHi x y).toNat)) * 2 ^ 256 +
            (c + (t + x * y)).toNat
        = ((UInt256.lt (c + (t + x * y)) c).toNat * 2 ^ 256 +
              (c + (t + x * y)).toNat) +
            ((UInt256.lt (t + x * y) t).toNat * 2 ^ 256 +
              (mulHi x y).toNat * 2 ^ 256) := by ring
      _ = (c.toNat + (t + x * y).toNat) +
            ((UInt256.lt (t + x * y) t).toNat * 2 ^ 256 +
              (mulHi x y).toNat * 2 ^ 256) := by rw [← h2]
      _ = (((UInt256.lt (t + x * y) t).toNat * 2 ^ 256 + (t + x * y).toNat) +
              (mulHi x y).toNat * 2 ^ 256) + c.toNat := by ring
      _ = ((t.toNat + (x * y).toNat) + (mulHi x y).toNat * 2 ^ 256) + c.toNat := by
            rw [← h1]
      _ = t.toNat + ((mulHi x y).toNat * 2 ^ 256 + (x * y).toNat) + c.toNat := by ring
      _ = t.toNat + x.toNat * y.toNat + c.toNat := by rw [hprod]
  have hbound : t.toNat + x.toNat * y.toNat + c.toNat < 2 ^ 256 * 2 ^ 256 :=
    total_lt ht hx hy hc
  have hlt : (UInt256.lt (c + (t + x * y)) c).toNat +
      ((UInt256.lt (t + x * y) t).toNat + (mulHi x y).toNat) < 2 ^ 256 := by
    by_contra hcon
    have hcon' : 2 ^ 256 ≤ (UInt256.lt (c + (t + x * y)) c).toNat +
        ((UInt256.lt (t + x * y) t).toNat + (mulHi x y).toNat) := Nat.le_of_not_lt hcon
    have hstep : 2 ^ 256 * 2 ^ 256 ≤
        ((UInt256.lt (c + (t + x * y)) c).toNat +
          ((UInt256.lt (t + x * y) t).toNat + (mulHi x y).toNat)) * 2 ^ 256 :=
      Nat.mul_le_mul_right _ hcon'
    have hle : ((UInt256.lt (c + (t + x * y)) c).toNat +
        ((UInt256.lt (t + x * y) t).toNat + (mulHi x y).toNat)) * 2 ^ 256 ≤
        t.toNat + x.toNat * y.toNat + c.toNat := by
      rw [← hkey]
      exact Nat.le_add_right _ _
    exact absurd hbound (Nat.not_lt.mpr (Nat.le_trans hstep hle))
  have hcarryVal : (macCarry x y t c).toNat =
      (UInt256.lt (c + (t + x * y)) c).toNat +
        ((UInt256.lt (t + x * y) t).toNat + (mulHi x y).toNat) := by
    simp only [macCarry, Challenge.EvmProof.Word.word_toNat_add]
    rw [Nat.mod_eq_of_lt (show (UInt256.lt (t + x * y) t).toNat +
        (mulHi x y).toNat < 2 ^ 256 by omega), Nat.mod_eq_of_lt hlt]
  rw [hcarryVal]
  exact hkey

/-! ## Pointer walks

Every loop pointer walks downwards by one limb per iteration.  The EVM adds
the wrapped constant `2 ^ 256 - 32`, so the `j`-th pointer of a walk starting
at `base` is `UInt256.ofNat (ptrAt base j)`. -/

def ptrAt (base j : Nat) : Nat :=
  base + j * 115792089237316195423570985008687907853269984665640564039457584007913129639904

@[simp] theorem ptrAt_zero (base : Nat) : ptrAt base 0 = base := by
  simp [ptrAt]

theorem ptrAt_succ (base j : Nat) :
    115792089237316195423570985008687907853269984665640564039457584007913129639904 +
        ptrAt base j = ptrAt base (j + 1) := by
  simp only [ptrAt, Nat.succ_mul]
  omega

theorem ptrAt_toNat (base j : Nat) (hj : 32 * j ≤ base) (hbase : base < 2 ^ 256) :
    (UInt256.ofNat (ptrAt base j)).toNat = base - 32 * j := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, ptrAt]
  have hlit : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
      Nat) = 2 ^ 256 - 32 := by norm_num
  have hmul : j * 115792089237316195423570985008687907853269984665640564039457584007913129639904
      = j * 2 ^ 256 - 32 * j := by
    rw [hlit, Nat.mul_sub, Nat.mul_comm j 32]
  rw [hmul]
  have hrewrite : base + (j * 2 ^ 256 - 32 * j) = (base - 32 * j) + j * 2 ^ 256 := by
    have hle : 32 * j ≤ j * 2 ^ 256 := by
      have := Nat.mul_le_mul_right j (show 32 ≤ 2 ^ 256 by norm_num)
      omega
    omega
  rw [hrewrite, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

theorem ptrAt_mod (base j : Nat) (hj : 32 * j ≤ base) (hbase : base < 2 ^ 256) :
    ptrAt base j %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      base - 32 * j := by
  have hlit : (115792089237316195423570985008687907853269984665640564039457584007913129639936 :
      Nat) = 2 ^ 256 := by norm_num
  rw [hlit, ← Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ptrAt_toNat base j hj hbase

/-! ## Active words

Every address `MONPRO` touches lies below `0x2500`, so once the setup block has
made `0x2500` bytes active no access here extends the high-water mark. -/

theorem activeWordsAfter_fix (curr off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 9472) (hcurr : 296 ≤ curr) :
    MachineState.activeWordsAfter curr off sz = curr := by
  unfold MachineState.activeWordsAfter
  simp only [hsz, if_false]
  have hle : (off + sz - 1) / 32 + 1 ≤ curr := by omega
  exact Nat.max_eq_left hle

theorem activeWords_fix (s : State) (off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 9472) (hact : 296 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat off sz) =
      s.activeWords := by
  rw [activeWordsAfter_fix _ off sz hsz hoff hact]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm

/-! ## The CIOS memory model

Addresses (absolute, independent of the code offset):
`T_ = 8192` holds `t[n+1]`, `TN = 8224` holds `t[n]`, `TS = 8256` holds the
`n` limbs `t[n-1..0]` most significant first, so `t[k]` sits at
`8256 + 32 * (n - 1 - k)` and `TL = 8224 + 32 * n` is the address of `t[0]`.
`V_S32 = 9344`, `V_MINV = 9376`, `V_ML = 9408`, `V_TL = 9440`. -/

/-- Memory together with a running carry. -/
structure MacState where
  memory : ByteArray
  carry : UInt256

/-- The `b` limb consumed by row `i`. -/
def rowBi (mem : ByteArray) (pb n i : Nat) : UInt256 :=
  MachineState.readWord mem (pb + 32 * (n - 1 - i))

/-- Memory and carry after `j` steps of the first limb loop of a row:
step `j` accumulates `a[j] * b[i]` into `t[j]`. -/
def l1Step (mem : ByteArray) (bi : UInt256) (pa n : Nat) : Nat → MacState
  | 0 => ⟨mem, UInt256.ofNat 0⟩
  | j + 1 =>
      let prev := l1Step mem bi pa n j
      let x := MachineState.readWord prev.memory (pa + 32 * (n - 1 - j))
      let t := MachineState.readWord prev.memory (8256 + 32 * (n - 1 - j))
      { memory := MachineState.writeBytes prev.memory
          (Data.Bytes.natToBytesPadded (macSum x bi t prev.carry).toNat 32)
          (8256 + 32 * (n - 1 - j))
        carry := macCarry x bi t prev.carry }

/-- `t[n] := t[n] + C`. -/
def midMem1 (mem : ByteArray) (c : UInt256) : ByteArray :=
  MachineState.writeBytes mem
    (Data.Bytes.natToBytesPadded (MachineState.readWord mem 8224 + c).toNat 32) 8224

/-- `t[n] := t[n] + C`, then `t[n+1] := carry`. -/
def midMem (mem : ByteArray) (c : UInt256) : ByteArray :=
  MachineState.writeBytes (midMem1 mem c)
    (Data.Bytes.natToBytesPadded
      (UInt256.lt (MachineState.readWord mem 8224 + c) c).toNat 32) 8192

/-- `mu = minv * t[0]` truncated to one limb. -/
def rowMu (mem : ByteArray) (n : Nat) : UInt256 :=
  MachineState.readWord mem 9376 * MachineState.readWord mem (8224 + 32 * n)

/-- The carry into the second limb loop: `t[0] + mu * m[0] = C * radix`. -/
def rowC0 (mem : ByteArray) (n : Nat) : UInt256 :=
  UInt256.isZero
      (UInt256.isZero (MachineState.readWord mem (32 * n - 32) * rowMu mem n)) +
    mulHi (MachineState.readWord mem (32 * n - 32)) (rowMu mem n)

/-- Memory and carry after `k` steps of the second limb loop.  Step `k`
accumulates `m[k+1] * mu` into `t[k+1]` and stores the result one limb down. -/
def l2Step (mem : ByteArray) (mu c0 : UInt256) (n : Nat) : Nat → MacState
  | 0 => ⟨mem, c0⟩
  | k + 1 =>
      let prev := l2Step mem mu c0 n k
      let x := MachineState.readWord prev.memory (32 * (n - 2 - k))
      let t := MachineState.readWord prev.memory (8256 + 32 * (n - 2 - k))
      { memory := MachineState.writeBytes prev.memory
          (Data.Bytes.natToBytesPadded (macSum x mu t prev.carry).toNat 32)
          (8256 + 32 * (n - 1 - k))
        carry := macCarry x mu t prev.carry }

/-- `t[n-1] := t[n] + C`. -/
def tailMem1 (mem : ByteArray) (c : UInt256) : ByteArray :=
  MachineState.writeBytes mem
    (Data.Bytes.natToBytesPadded (MachineState.readWord mem 8224 + c).toNat 32) 8256

/-- `t[n-1] := t[n] + C`, then `t[n] := t[n+1] + carry`. -/
def tailMem (mem : ByteArray) (c : UInt256) : ByteArray :=
  MachineState.writeBytes (tailMem1 mem c)
    (Data.Bytes.natToBytesPadded
      (MachineState.readWord (tailMem1 mem c) 8192 +
        UInt256.lt (MachineState.readWord mem 8224 + c) c).toNat 32) 8224

/-- The first limb loop of row `i`, run to completion. -/
def rowL1 (mem : ByteArray) (pa pb n i : Nat) : MacState :=
  l1Step mem (rowBi mem pb n i) pa n n

/-- Memory after the middle block of row `i`. -/
def rowMid (mem : ByteArray) (pa pb n i : Nat) : ByteArray :=
  midMem (rowL1 mem pa pb n i).memory (rowL1 mem pa pb n i).carry

/-- The second limb loop of row `i`, run to completion. -/
def rowL2 (mem : ByteArray) (pa pb n i : Nat) : MacState :=
  l2Step (rowMid mem pa pb n i) (rowMu (rowL1 mem pa pb n i).memory n)
    (rowC0 (rowL1 mem pa pb n i).memory n) n (n - 1)

/-- Memory after row `i`. -/
def rowMem (mem : ByteArray) (pa pb n i : Nat) : ByteArray :=
  tailMem (rowL2 mem pa pb n i).memory (rowL2 mem pa pb n i).carry

/-- Memory after `i` complete CIOS rows. -/
def rowsMem (mem : ByteArray) (pa pb n : Nat) : Nat → ByteArray
  | 0 => mem
  | i + 1 => rowMem (rowsMem mem pa pb n i) pa pb n i

/-- The prologue zeroes `t[n+1 .. 0]` with `CALLDATACOPY` from the end of the
calldata. -/
def mpZeroed (s : State) (mem : ByteArray) (n : Nat) : ByteArray :=
  MachineState.writeBytes mem
    (MachineState.readPadded s.executionEnv.calldata s.executionEnv.calldata.size
      (64 + 32 * n)) 8192

/-! ## States at the block boundaries

Loop heads carry their iteration index so the `iterateBounded` families are
indexed state functions; the block-exit states take the popped stack entries
as opaque parameters, which keeps every reduction lemma stated over an
arbitrary state constrained only by its `pc` and stack shape. -/

/-- Subroutine entry, pc 1939, stack `[pa, pb, pd, ret]`. -/
def mpEntryState (s : State) (mem : ByteArray) (pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1939
           stack := [UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
           memory := mem }

/-- The outer loop head, pc 1974, at the start of row `i`. -/
def mpOutState (s : State) (mem : ByteArray) (pa pb n i : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1974
           stack := [UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32), pdst, ret] ++ rest
           memory := mem }

/-- The first limb loop head, pc 1995, after `j` steps of row `i`. -/
def mpL1State (s : State) (mem : ByteArray) (bi : UInt256) (pa pb n i j : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1995
           stack := [UInt256.ofNat (ptrAt (pa + 32 * n - 32) j),
                     UInt256.ofNat (ptrAt (8224 + 32 * n) j),
                     (l1Step mem bi pa n j).carry, bi,
                     UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32), pdst, ret] ++ rest
           memory := (l1Step mem bi pa n j).memory }

/-- The row middle, pc 2141.  The two spent loop pointers are popped at once,
so they stay opaque. -/
def mpMidState (s : State) (mem : ByteArray) (paj ptj c bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2141
           stack := [paj, ptj, c, bi, UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32), pdst, ret] ++ rest
           memory := mem }

/-- The second limb loop head, pc 2241, after `k` steps of row `i`. -/
def mpL2State (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2241
           stack := [UInt256.ofNat (ptrAt (32 * n - 64) k),
                     UInt256.ofNat (ptrAt (8192 + 32 * n) k),
                     (l2Step mid mu c0 n k).carry, mu, bi,
                     UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32), pdst, ret] ++ rest
           memory := (l2Step mid mu c0 n k).memory }

/-- The row tail, pc 2392. -/
def mpTailState (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2392
           stack := [pmj, ptj, c, mu, bi, UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32), pdst, ret] ++ rest
           memory := mem }

/-- The subroutine exit, pc 2460, after all `n` rows. -/
def mpExitState (s : State) (mem : ByteArray) (pbi : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2460
           stack := [pbi, UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32),
                     pdst, ret] ++ rest
           memory := mem }

/-- `CSUB` entry, pc 2642, with stack `[pd, ret]`. -/
def mpCsubState (s : State) (mem : ByteArray) (pdst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2642
           stack := [pdst, ret] ++ rest
           memory := mem }

/-! ## The prologue and the outer loop head -/

set_option linter.unusedSimpArgs false in
theorem run_mpEntry (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n)) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1379
      (mpEntryState s mem pa pb pdst ret rest) =
      some (mpOutState s (mpZeroed s mem n) pa pb n 0 pdst ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h64 : (64 : UInt256) = UInt256.ofNat 64 := by decide
  have h8192 : (8192 : UInt256).toNat = 8192 := by decide
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  have hsizeN : (64 + 32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      64 + 32 * n := Nat.mod_eq_of_lt (by omega)
  have hcdsN : s.executionEnv.calldata.size %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      s.executionEnv.calldata.size := Nat.mod_eq_of_lt (by omega)
  have hsub1 : UInt256.ofNat (pb + 32 * n) - UInt256.ofNat 32 =
      UInt256.ofNat (pb + 32 * n - 32) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)
  have hsub2 : UInt256.ofNat pb - UInt256.ofNat 32 = UInt256.ofNat (pb - 32) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)
  have hsub3 : UInt256.ofNat pa - UInt256.ofNat 32 = UInt256.ofNat (pa - 32) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)
  have hactS : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9344 32) = s.activeWords :=
    activeWords_fix s 9344 32 (by decide) (by omega) hact
  have hactC : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 8192 (64 + 32 * n)) =
      s.activeWords := activeWords_fix s 8192 (64 + 32 * n) (by omega) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [blk1379, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      mpEntryState, mpOutState, mpZeroed, fastPC10,
      hc4, hc5, hc6, hc7, hc8, hrun, h32, h64, h8192, h9344, hs32,
      hsizeN, hcdsN, hsub1, hsub2, hsub3, hactS, hactC,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_mpOut (s : State) (mem : ByteArray) (pa pb n i : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (_hn : 2 ≤ n) (_hn32 : n ≤ 32) (hi : i < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n)) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1406
      (mpOutState s mem pa pb n i pdst ret rest) =
      some (mpL1State s mem (rowBi mem pb n i) pa pb n i 0 pdst ret rest) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  have h9440 : (9440 : UInt256).toNat = 9440 := by decide
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hpbi : ptrAt (pb + 32 * n - 32) i %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pb + 32 * (n - 1 - i) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hpa32 : 32 + (pa - 32) = pa := by omega
  have hsuba : UInt256.ofNat (32 * n + pa) - UInt256.ofNat 32 =
      UInt256.ofNat (pa + 32 * n - 32) := by
    rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)]
    exact congrArg UInt256.ofNat (by omega)
  have hactB : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pb + 32 * (n - 1 - i)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9440 32) = s.activeWords :=
    activeWords_fix s 9440 32 (by decide) (by omega) hact
  have hactS : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9344 32) = s.activeWords :=
    activeWords_fix s 9344 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [blk1406, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      mpOutState, mpL1State, l1Step, rowBi, fastPC10, fastPC11,
      hc5, hc6, hc7, hc8, hc9, hc10, hrun, h32, h9344, h9440, hzero,
      hs32, htl, hpbi, hpa32, hsuba, hactB, hactT, hactS,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

/-! ## The first limb loop -/

/-- The `PUSH32` immediate in the `MULMOD`, folded into `maxWord`. -/
theorem maxWord_literal :
    (115792089237316195423570985008687907853269984665640564039457584007913129639935 :
      UInt256) = maxWord := rfl

set_option linter.unusedSimpArgs false in
theorem run_mpL1Body (s : State) (mem : ByteArray) (bi : UInt256) (pa pb n i j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hj : j + 1 < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1421
      (mpL1State s mem bi pa pb n i j pdst ret rest) =
      some (mpL1State s mem bi pa pb n i (j + 1) pdst ret rest) := by
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hK : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
      UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have h1995 : (1995 : UInt256).toNat = 1995 := by decide
  have h1995' : (1995 : UInt256) = UInt256.ofNat 1995 := by decide
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (1995 : UInt256).toNat = true := by
    rw [h1995]; exact jumpDest1995
  have hpaj : ptrAt (pa + 32 * n - 32) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hptj : ptrAt (8224 + 32 * n) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hnextA : ptrAt (pa + 32 * n - 32) (j + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa + 32 * (n - 2 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hpamN : (pa - 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa - 32 := Nat.mod_eq_of_lt (by omega)
  have hgt : pa - 32 < pa + 32 * (n - 2 - j) := by omega
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pa + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [blk1421, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      mpL1State, l1Step, macSum, macCarry, mulHi, maxWord_literal,
      fastPC11, fastPC12,
      hc9, hc10, hc11, hc12, hc13, hrun, hcode, hK, h1995, h1995', hjump,
      jumpDest1995, hpaj, hptj, hnextA, hpamN, hgt, hactA, hactT, ptrAt_succ,
      UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_mpL1Exit (s : State) (mem : ByteArray) (bi : UInt256) (pa pb n i j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hj : j + 1 = n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1421
      (mpL1State s mem bi pa pb n i j pdst ret rest) =
      some (mpMidState s (l1Step mem bi pa n (j + 1)).memory
        (UInt256.ofNat (ptrAt (pa + 32 * n - 32) (j + 1)))
        (UInt256.ofNat (ptrAt (8224 + 32 * n) (j + 1)))
        (l1Step mem bi pa n (j + 1)).carry bi pa pb n i pdst ret rest) := by
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hK : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
      UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have hpaj : ptrAt (pa + 32 * n - 32) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hptj : ptrAt (8224 + 32 * n) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hnextA : ptrAt (pa + 32 * n - 32) (j + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa - 32 := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hpamN : (pa - 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa - 32 := Nat.mod_eq_of_lt (by omega)
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pa + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [blk1421, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      mpL1State, mpMidState, l1Step, macSum, macCarry, mulHi, maxWord_literal,
      fastPC11, fastPC12,
      hc9, hc10, hc11, hc12, hc13, hrun, hK,
      hpaj, hptj, hnextA, hpamN, hactA, hactT, ptrAt_succ,
      UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

/-! ## The row middle

`(C, t[n]) := t[n] + C`; `t[n+1] := carry`; `mu := minv * t[0]`; and the carry
into the second loop from `t[0] + mu * m[0] = C * radix`. -/

/-- The two `MSTORE`s of the row middle land at `8224` and `8192`, so every
other word the block reads still has its pre-middle value. -/
theorem readWord_midMem_peel (mem : ByteArray) (v w r : Nat)
    (hr : r + 32 ≤ 8192 ∨ 8256 ≤ r) :
    MachineState.readWord
        (MachineState.writeBytes
          (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 8224)
          (Data.Bytes.natToBytesPadded w 32) 8192) r =
      MachineState.readWord mem r := by
  have h1 : MachineState.readWord
      (MachineState.writeBytes
        (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 8224)
        (Data.Bytes.natToBytesPadded w 32) 8192) r =
      MachineState.readWord
        (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 8224) r := by
    apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  have h2 : MachineState.readWord
      (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 8224) r =
      MachineState.readWord mem r := by
    apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  rw [h1, h2]

set_option linter.unusedSimpArgs false in
theorem run_mpMid (s : State) (mem : ByteArray) (paj ptj c bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n)) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1469
      (mpMidState s mem paj ptj c bi pa pb n i pdst ret rest) =
      some (mpL2State s (midMem mem c) bi (rowMu mem n)
        (rowC0 mem n) pa pb n i 0 pdst ret rest) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h8192 : (8192 : UInt256).toNat = 8192 := by decide
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have h9376 : (9376 : UInt256).toNat = 9376 := by decide
  have h9408 : (9408 : UInt256).toNat = 9408 := by decide
  have h9440 : (9440 : UInt256).toNat = 9440 := by decide
  have hTLN : (8224 + 32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8224 + 32 * n := Nat.mod_eq_of_lt (by omega)
  have hMLN : (32 * n - 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * n - 32 := Nat.mod_eq_of_lt (by omega)
  have hsc1 : 8256 ≤ 8224 + 32 * n := by omega
  have hsc2 : 32 * n - 32 + 32 ≤ 8192 := by omega
  have hsc3 : 32 * n ≤ 8192 := by omega
  have hsubTL : UInt256.ofNat (8224 + 32 * n) - UInt256.ofNat 32 =
      UInt256.ofNat (8192 + 32 * n) := by
    rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)]
    exact congrArg UInt256.ofNat (by omega)
  have hsubML : UInt256.ofNat (32 * n - 32) - UInt256.ofNat 32 =
      UInt256.ofNat (32 * n - 64) := by
    rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)]
    exact congrArg UInt256.ofNat (by omega)
  have hactN : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 8224 32) = s.activeWords :=
    activeWords_fix s 8224 32 (by decide) (by omega) hact
  have hactP : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 8192 32) = s.activeWords :=
    activeWords_fix s 8192 32 (by decide) (by omega) hact
  have hactTL : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9440 32) = s.activeWords :=
    activeWords_fix s 9440 32 (by decide) (by omega) hact
  have hactT0 : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat (8224 + 32 * n) 32) =
      s.activeWords := activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactMI : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9376 32) = s.activeWords :=
    activeWords_fix s 9376 32 (by decide) (by omega) hact
  have hactML : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9408 32) = s.activeWords :=
    activeWords_fix s 9408 32 (by decide) (by omega) hact
  have hactM0 : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat (32 * n - 32) 32) =
      s.activeWords := activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [blk1469, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      mpMidState, mpL2State, l2Step, midMem, midMem1, rowMu, rowC0, mulHi,
      maxWord_literal, fastPC12, fastPC13, readWord_midMem_peel,
      hc6, hc7, hc8, hc9, hc10, hc11, hrun, h32, h8192, h8224, h9376, h9408, h9440,
      hml, htl, hTLN, hMLN, hsubTL, hsubML, hsc1, hsc2, hsc3,
      hactN, hactP, hactTL, hactT0, hactMI, hactML, hactM0,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

/-! ## The second limb loop -/

theorem ptrAt_shift32 (n k : Nat) :
    32 + ptrAt (8192 + 32 * n) k = ptrAt (8224 + 32 * n) k := by
  simp only [ptrAt]
  omega

set_option linter.unusedSimpArgs false in
theorem run_mpL2Body (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hk : k + 2 < n) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1519
      (mpL2State s mid bi mu c0 pa pb n i k pdst ret rest) =
      some (mpL2State s mid bi mu c0 pa pb n i (k + 1) pdst ret rest) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hK : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
      UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have h2241 : (2241 : UInt256).toNat = 2241 := by decide
  have h2241' : (2241 : UInt256) = UInt256.ofNat 2241 := by decide
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (2241 : UInt256).toNat = true := by
    rw [h2241]; exact jumpDest2241
  have hpmj : ptrAt (32 * n - 64) k %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * (n - 2 - k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hptj : ptrAt (8192 + 32 * n) k %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 2 - k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hwr : ptrAt (8224 + 32 * n) k %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 1 - k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hnextT : ptrAt (8192 + 32 * n) (k + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8160 + 32 * n - 32 * k := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hgt : 8224 < 8160 + 32 * n - 32 * k := by omega
  have hactM : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (32 * (n - 2 - k)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 2 - k)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactW : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 1 - k)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [blk1519, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      mpL2State, l2Step, macSum, macCarry, mulHi, maxWord_literal,
      fastPC13, fastPC14,
      hc10, hc11, hc12, hc13, hc14, hrun, hcode, hK, h32, h8224,
      h2241, h2241', hjump, jumpDest2241,
      hpmj, hptj, hwr, hnextT, hgt, hactM, hactT, hactW, ptrAt_succ, ptrAt_shift32,
      UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_mpL2Exit (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hk : k + 2 = n) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1519
      (mpL2State s mid bi mu c0 pa pb n i k pdst ret rest) =
      some (mpTailState s (l2Step mid mu c0 n (k + 1)).memory
        (UInt256.ofNat (ptrAt (32 * n - 64) (k + 1)))
        (UInt256.ofNat (ptrAt (8192 + 32 * n) (k + 1)))
        (l2Step mid mu c0 n (k + 1)).carry mu bi pa pb n i pdst ret rest) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hK : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
      UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have hpmj : ptrAt (32 * n - 64) k %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * (n - 2 - k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hptj : ptrAt (8192 + 32 * n) k %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 2 - k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hwr : ptrAt (8224 + 32 * n) k %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 1 - k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hnextT : ptrAt (8192 + 32 * n) (k + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8224 := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hactM : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (32 * (n - 2 - k)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 2 - k)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactW : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 1 - k)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [blk1519, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      mpL2State, mpTailState, l2Step, macSum, macCarry, mulHi, maxWord_literal,
      fastPC13, fastPC14,
      hc10, hc11, hc12, hc13, hc14, hrun, hK, h32, h8224,
      hpmj, hptj, hwr, hnextT, hactM, hactT, hactW, ptrAt_succ, ptrAt_shift32,
      UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

/-! ## The row tail, the outer loop back edge and the tail call -/

set_option linter.unusedSimpArgs false in
theorem run_mpTailNext (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (_hn32 : n ≤ 32) (hi : i + 1 < n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1569
      (mpTailState s mem pmj ptj c mu bi pa pb n i pdst ret rest) =
      some (mpOutState s (tailMem mem c) pa pb n (i + 1) pdst ret rest) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hK : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
      UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have h8192 : (8192 : UInt256).toNat = 8192 := by decide
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have h8256 : (8256 : UInt256).toNat = 8256 := by decide
  have h1974 : (1974 : UInt256).toNat = 1974 := by decide
  have h1974' : (1974 : UInt256) = UInt256.ofNat 1974 := by decide
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (1974 : UInt256).toNat = true := by
    rw [h1974]; exact jumpDest1974
  have hnextB : ptrAt (pb + 32 * n - 32) (i + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pb + 32 * (n - 2 - i) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hpbmN : (pb - 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pb - 32 := Nat.mod_eq_of_lt (by omega)
  have hgt : pb - 32 < pb + 32 * (n - 2 - i) := by omega
  have hactN : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 8224 32) = s.activeWords :=
    activeWords_fix s 8224 32 (by decide) (by omega) hact
  have hactS : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 8256 32) = s.activeWords :=
    activeWords_fix s 8256 32 (by decide) (by omega) hact
  have hactP : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 8192 32) = s.activeWords :=
    activeWords_fix s 8192 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [blk1569, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      mpTailState, mpOutState, tailMem, tailMem1, fastPC14, fastPC15,
      hc5, hc6, hc7, hc8, hc9, hc10, hrun, hcode, hK, h8192, h8224, h8256,
      h1974, h1974', hjump, jumpDest1974, hnextB, hpbmN, hgt,
      hactN, hactS, hactP, ptrAt_succ,
      UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_mpTailLast (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (_hn32 : n ≤ 32) (hi : i + 1 = n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1569
      (mpTailState s mem pmj ptj c mu bi pa pb n i pdst ret rest) =
      some (mpExitState s (tailMem mem c)
        (UInt256.ofNat (ptrAt (pb + 32 * n - 32) (i + 1))) pa pb pdst ret rest) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hK : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
      UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have h8192 : (8192 : UInt256).toNat = 8192 := by decide
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have h8256 : (8256 : UInt256).toNat = 8256 := by decide
  have hnextB : ptrAt (pb + 32 * n - 32) (i + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pb - 32 := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hpbmN : (pb - 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pb - 32 := Nat.mod_eq_of_lt (by omega)
  have hactN : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 8224 32) = s.activeWords :=
    activeWords_fix s 8224 32 (by decide) (by omega) hact
  have hactS : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 8256 32) = s.activeWords :=
    activeWords_fix s 8256 32 (by decide) (by omega) hact
  have hactP : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 8192 32) = s.activeWords :=
    activeWords_fix s 8192 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [blk1569, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      mpTailState, mpExitState, tailMem, tailMem1, fastPC14, fastPC15,
      hc5, hc6, hc7, hc8, hc9, hc10, hrun, hK, h8192, h8224, h8256,
      hnextB, hpbmN, hactN, hactS, hactP, ptrAt_succ,
      UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_mpExit (s : State) (mem : ByteArray) (pbi : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1595
      (mpExitState s mem pbi pa pb pdst ret rest) =
      some (mpCsubState s mem pdst ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have h2642 : (2642 : UInt256).toNat = 2642 := by decide
  have h2642' : (2642 : UInt256) = UInt256.ofNat 2642 := by decide
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (2642 : UInt256).toNat = true := by
    rw [h2642]; exact jumpDest2642
  simp (config := { maxSteps := 400000 })
    [blk1595, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      mpExitState, mpCsubState, fastPC15,
      hc2, hc3, hc4, hc5, hrun, hcode, h2642, h2642', hjump, jumpDest2642,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

/-! ## Memory preservation

Every word `MONPRO` writes lies in `[8192, 9280)`: the `CALLDATACOPY` prologue
writes `64 + 32 * n ≤ 1088` bytes from `8192`, and every limb store lands at
`8256 + 32 * (n - 1 - j) ≤ 9248`.  So every word below `T_ = 0x2000` — that is
every named block `M`, `ACC`, `BASE`, `ONE`, `R1`, `CC`, `RR`, `SUBB` of the
memory map — and every word at or above `9280` — `V_S32 = 9344`,
`V_MINV = 9376`, `V_ML = 9408`, `V_TL = 9440`, `V_EOFF`, `V_N` — survive the
subroutine unchanged. -/

theorem readWord_writeLimb (mem : ByteArray) (w dst addr : Nat)
    (hdstLo : 8192 ≤ dst) (hdstHi : dst + 32 ≤ 9280)
    (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord
        (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded w 32) dst) addr =
      MachineState.readWord mem addr := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega

theorem readWord_l1Step (mem : ByteArray) (bi : UInt256) (pa n addr j : Nat)
    (hn : n ≤ 32) (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (l1Step mem bi pa n j).memory addr =
      MachineState.readWord mem addr := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [l1Step]
      rw [readWord_writeLimb _ _ _ _ (by omega) (by omega) haddr]
      exact ih

theorem readWord_l2Step (mem : ByteArray) (mu c0 : UInt256) (n addr k : Nat)
    (hn : n ≤ 32) (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (l2Step mem mu c0 n k).memory addr =
      MachineState.readWord mem addr := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [l2Step]
      rw [readWord_writeLimb _ _ _ _ (by omega) (by omega) haddr]
      exact ih

theorem readWord_midMem1 (mem : ByteArray) (c : UInt256) (addr : Nat)
    (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (midMem1 mem c) addr = MachineState.readWord mem addr := by
  simp only [midMem1]
  rw [readWord_writeLimb _ _ _ _ (by omega) (by omega) haddr]

theorem readWord_midMem (mem : ByteArray) (c : UInt256) (addr : Nat)
    (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (midMem mem c) addr = MachineState.readWord mem addr := by
  simp only [midMem]
  rw [readWord_writeLimb _ _ _ _ (by omega) (by omega) haddr,
    readWord_midMem1 _ _ _ haddr]

theorem readWord_tailMem1 (mem : ByteArray) (c : UInt256) (addr : Nat)
    (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (tailMem1 mem c) addr = MachineState.readWord mem addr := by
  simp only [tailMem1]
  rw [readWord_writeLimb _ _ _ _ (by omega) (by omega) haddr]

theorem readWord_tailMem (mem : ByteArray) (c : UInt256) (addr : Nat)
    (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (tailMem mem c) addr = MachineState.readWord mem addr := by
  simp only [tailMem]
  rw [readWord_writeLimb _ _ _ _ (by omega) (by omega) haddr,
    readWord_tailMem1 _ _ _ haddr]

theorem readWord_rowMid (mem : ByteArray) (pa pb n i addr : Nat)
    (hn : n ≤ 32) (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (rowMid mem pa pb n i) addr =
      MachineState.readWord mem addr := by
  simp only [rowMid, rowL1]
  rw [readWord_midMem _ _ _ haddr, readWord_l1Step _ _ _ _ _ _ hn haddr]

theorem readWord_rowMem (mem : ByteArray) (pa pb n i addr : Nat)
    (hn : n ≤ 32) (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (rowMem mem pa pb n i) addr =
      MachineState.readWord mem addr := by
  simp only [rowMem, rowL2]
  rw [readWord_tailMem _ _ _ haddr, readWord_l2Step _ _ _ _ _ _ hn haddr,
    readWord_rowMid _ _ _ _ _ _ hn haddr]

theorem readWord_rowsMem (mem : ByteArray) (pa pb n addr : Nat)
    (hn : n ≤ 32) (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) : ∀ i,
    MachineState.readWord (rowsMem mem pa pb n i) addr =
      MachineState.readWord mem addr := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [rowsMem, readWord_rowMem _ _ _ _ _ _ hn haddr]
      exact ih

theorem readWord_mpZeroed (s : State) (mem : ByteArray) (n addr : Nat)
    (hn : n ≤ 32) (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (mpZeroed s mem n) addr = MachineState.readWord mem addr := by
  simp only [mpZeroed]
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [Challenge.EvmProof.Memory.readPadded_size]
  omega

/-! ## Gas traces for the individual blocks -/

def gasSteps_mpEntry (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n)) :
    Challenge.EvmProof.GasSteps
      (mpEntryState s mem pa pb pdst ret rest)
      (mpOutState s (mpZeroed s mem n) pa pb n 0 pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1379 hcode hfork
    (run_mpEntry s mem pa pb n pdst ret rest hcap hrun hact hn hn32 hpa hpaFit
      hpb hpbFit hcds hs32) hrun hnp

def gasSteps_mpOut (s : State) (mem : ByteArray) (pa pb n i : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32) (hi : i < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n)) :
    Challenge.EvmProof.GasSteps
      (mpOutState s mem pa pb n i pdst ret rest)
      (mpL1State s mem (rowBi mem pb n i) pa pb n i 0 pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1406 hcode hfork
    (run_mpOut s mem pa pb n i pdst ret rest hcap hrun hact hn hn32 hi hpa hpaFit
      hpb hpbFit hs32 htl) hrun hnp

def gasSteps_mpL1Body (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hj : j + 1 < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (mpL1State s mem bi pa pb n i j pdst ret rest)
      (mpL1State s mem bi pa pb n i (j + 1) pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1421 hcode hfork
    (run_mpL1Body s mem bi pa pb n i j pdst ret rest hcap hrun hcode hact hn32 hj
      hpa hpaFit) hrun hnp

def gasSteps_mpL1Loop (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb m i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : m + 2 ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * (m + 2) ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (mpL1State s mem bi pa pb (m + 2) i 0 pdst ret rest)
      (mpL1State s mem bi pa pb (m + 2) i (m + 1) pdst ret rest) :=
  Challenge.EvmProof.GasSteps.iterateBounded
    (I := fun j => mpL1State s mem bi pa pb (m + 2) i j pdst ret rest) (m + 1)
    (fun j hj => gasSteps_mpL1Body s mem bi pa pb (m + 2) i j pdst ret rest hcap
      hrun hcode hfork hnp hact hn32 (by omega) hpa hpaFit)

def gasSteps_mpL1Exit (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hj : j + 1 = n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (mpL1State s mem bi pa pb n i j pdst ret rest)
      (mpMidState s (l1Step mem bi pa n (j + 1)).memory
        (UInt256.ofNat (ptrAt (pa + 32 * n - 32) (j + 1)))
        (UInt256.ofNat (ptrAt (8224 + 32 * n) (j + 1)))
        (l1Step mem bi pa n (j + 1)).carry bi pa pb n i pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1421 hcode hfork
    (run_mpL1Exit s mem bi pa pb n i j pdst ret rest hcap hrun hact hn32 hj hpa
      hpaFit) hrun hnp

def gasSteps_mpMid (s : State) (mem : ByteArray) (paj ptj c bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n)) :
    Challenge.EvmProof.GasSteps
      (mpMidState s mem paj ptj c bi pa pb n i pdst ret rest)
      (mpL2State s (midMem mem c) bi (rowMu mem n)
        (rowC0 mem n) pa pb n i 0 pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1469 hcode hfork
    (run_mpMid s mem paj ptj c bi pa pb n i pdst ret rest hcap hrun hact hn hn32
      hml htl) hrun hnp

def gasSteps_mpL2Body (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hk : k + 2 < n) :
    Challenge.EvmProof.GasSteps
      (mpL2State s mid bi mu c0 pa pb n i k pdst ret rest)
      (mpL2State s mid bi mu c0 pa pb n i (k + 1) pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1519 hcode hfork
    (run_mpL2Body s mid bi mu c0 pa pb n i k pdst ret rest hcap hrun hcode hact
      hn32 hk) hrun hnp

def gasSteps_mpL2Loop (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb m i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : m + 2 ≤ 32) :
    Challenge.EvmProof.GasSteps
      (mpL2State s mid bi mu c0 pa pb (m + 2) i 0 pdst ret rest)
      (mpL2State s mid bi mu c0 pa pb (m + 2) i m pdst ret rest) :=
  Challenge.EvmProof.GasSteps.iterateBounded
    (I := fun k => mpL2State s mid bi mu c0 pa pb (m + 2) i k pdst ret rest) m
    (fun k hk => gasSteps_mpL2Body s mid bi mu c0 pa pb (m + 2) i k pdst ret rest
      hcap hrun hcode hfork hnp hact hn32 (by omega))

def gasSteps_mpL2Exit (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hk : k + 2 = n) :
    Challenge.EvmProof.GasSteps
      (mpL2State s mid bi mu c0 pa pb n i k pdst ret rest)
      (mpTailState s (l2Step mid mu c0 n (k + 1)).memory
        (UInt256.ofNat (ptrAt (32 * n - 64) (k + 1)))
        (UInt256.ofNat (ptrAt (8192 + 32 * n) (k + 1)))
        (l2Step mid mu c0 n (k + 1)).carry mu bi pa pb n i pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1519 hcode hfork
    (run_mpL2Exit s mid bi mu c0 pa pb n i k pdst ret rest hcap hrun hact hn32 hk)
    hrun hnp

def gasSteps_mpTailNext (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hi : i + 1 < n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (mpTailState s mem pmj ptj c mu bi pa pb n i pdst ret rest)
      (mpOutState s (tailMem mem c) pa pb n (i + 1) pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1569 hcode hfork
    (run_mpTailNext s mem pmj ptj c mu bi pa pb n i pdst ret rest hcap hrun hcode
      hact hn32 hi hpb hpbFit) hrun hnp

def gasSteps_mpTailLast (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hi : i + 1 = n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (mpTailState s mem pmj ptj c mu bi pa pb n i pdst ret rest)
      (mpExitState s (tailMem mem c)
        (UInt256.ofNat (ptrAt (pb + 32 * n - 32) (i + 1))) pa pb pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1569 hcode hfork
    (run_mpTailLast s mem pmj ptj c mu bi pa pb n i pdst ret rest hcap hrun hact
      hn32 hi hpb hpbFit) hrun hnp

def gasSteps_mpExit (s : State) (mem : ByteArray) (pbi : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (mpExitState s mem pbi pa pb pdst ret rest)
      (mpCsubState s mem pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1595 hcode hfork
    (run_mpExit s mem pbi pa pb pdst ret rest hcap hrun hcode) hrun hnp

/-! ## One CIOS row and the outer loop

The limb count is written `m + 2` throughout the composition: that is exactly
the range `2 ≤ n ≤ 32` the fast path guarantees, and it keeps `n - 1` and
`n - 2` out of the loop indices. -/

theorem rowMid_eq (mem : ByteArray) (pa pb m i : Nat) :
    midMem (l1Step mem (rowBi mem pb (m + 2) i) pa (m + 2) (m + 1 + 1)).memory
        (l1Step mem (rowBi mem pb (m + 2) i) pa (m + 2) (m + 1 + 1)).carry =
      rowMid mem pa pb (m + 2) i := rfl

theorem rowL2_eq (mem : ByteArray) (pa pb m i : Nat) :
    l2Step (rowMid mem pa pb (m + 2) i)
        (rowMu (rowL1 mem pa pb (m + 2) i).memory (m + 2))
        (rowC0 (rowL1 mem pa pb (m + 2) i).memory (m + 2)) (m + 2) (m + 1) =
      rowL2 mem pa pb (m + 2) i := rfl

theorem rowMem_eq (mem : ByteArray) (pa pb m i : Nat) :
    tailMem (rowL2 mem pa pb (m + 2) i).memory (rowL2 mem pa pb (m + 2) i).carry =
      rowMem mem pa pb (m + 2) i := rfl

def gasSteps_mpRowToTail (s : State) (mem : ByteArray) (pa pb m i : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : m + 2 ≤ 32) (hi : i < m + 2)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * (m + 2) ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * (m + 2) ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * (m + 2)))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * (m + 2)))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * (m + 2) - 32)) :
    Challenge.EvmProof.GasSteps
      (mpOutState s mem pa pb (m + 2) i pdst ret rest)
      (mpTailState s (rowL2 mem pa pb (m + 2) i).memory
        (UInt256.ofNat (ptrAt (32 * (m + 2) - 64) (m + 1)))
        (UInt256.ofNat (ptrAt (8192 + 32 * (m + 2)) (m + 1)))
        (rowL2 mem pa pb (m + 2) i).carry
        (rowMu (rowL1 mem pa pb (m + 2) i).memory (m + 2))
        (rowBi mem pb (m + 2) i) pa pb (m + 2) i pdst ret rest) :=
  (gasSteps_mpOut s mem pa pb (m + 2) i pdst ret rest hcap hrun hcode hfork hnp
      hact (by omega) hn32 hi hpa hpaFit hpb hpbFit hs32 htl).trans <|
  (gasSteps_mpL1Loop s mem (rowBi mem pb (m + 2) i) pa pb m i pdst ret rest hcap
      hrun hcode hfork hnp hact hn32 hpa hpaFit).trans <|
  (gasSteps_mpL1Exit s mem (rowBi mem pb (m + 2) i) pa pb (m + 2) i (m + 1) pdst
      ret rest hcap hrun hcode hfork hnp hact hn32 rfl hpa hpaFit).trans <|
  (gasSteps_mpMid s
      (l1Step mem (rowBi mem pb (m + 2) i) pa (m + 2) (m + 1 + 1)).memory
      (UInt256.ofNat (ptrAt (pa + 32 * (m + 2) - 32) (m + 1 + 1)))
      (UInt256.ofNat (ptrAt (8224 + 32 * (m + 2)) (m + 1 + 1)))
      (l1Step mem (rowBi mem pb (m + 2) i) pa (m + 2) (m + 1 + 1)).carry
      (rowBi mem pb (m + 2) i) pa pb (m + 2) i pdst ret rest hcap hrun hcode hfork
      hnp hact (by omega) hn32
      ((readWord_l1Step mem (rowBi mem pb (m + 2) i) pa (m + 2) 9408 (m + 1 + 1)
          hn32 (by omega)).trans hml)
      ((readWord_l1Step mem (rowBi mem pb (m + 2) i) pa (m + 2) 9440 (m + 1 + 1)
          hn32 (by omega)).trans htl)).trans <|
  (gasSteps_mpL2Loop s (rowMid mem pa pb (m + 2) i) (rowBi mem pb (m + 2) i)
      (rowMu (rowL1 mem pa pb (m + 2) i).memory (m + 2))
      (rowC0 (rowL1 mem pa pb (m + 2) i).memory (m + 2)) pa pb m i pdst ret rest
      hcap hrun hcode hfork hnp hact hn32).trans
  (gasSteps_mpL2Exit s (rowMid mem pa pb (m + 2) i) (rowBi mem pb (m + 2) i)
      (rowMu (rowL1 mem pa pb (m + 2) i).memory (m + 2))
      (rowC0 (rowL1 mem pa pb (m + 2) i).memory (m + 2)) pa pb (m + 2) i m pdst ret
      rest hcap hrun hcode hfork hnp hact hn32 rfl)

def gasSteps_mpRowNext (s : State) (mem : ByteArray) (pa pb m i : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : m + 2 ≤ 32) (hi : i + 1 < m + 2)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * (m + 2) ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * (m + 2) ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * (m + 2)))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * (m + 2)))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * (m + 2) - 32)) :
    Challenge.EvmProof.GasSteps
      (mpOutState s mem pa pb (m + 2) i pdst ret rest)
      (mpOutState s (rowMem mem pa pb (m + 2) i) pa pb (m + 2) (i + 1) pdst ret
        rest) :=
  (gasSteps_mpRowToTail s mem pa pb m i pdst ret rest hcap hrun hcode hfork hnp
      hact hn32 (by omega) hpa hpaFit hpb hpbFit hs32 htl hml).trans
    (gasSteps_mpTailNext s (rowL2 mem pa pb (m + 2) i).memory
      (UInt256.ofNat (ptrAt (32 * (m + 2) - 64) (m + 1)))
      (UInt256.ofNat (ptrAt (8192 + 32 * (m + 2)) (m + 1)))
      (rowL2 mem pa pb (m + 2) i).carry
      (rowMu (rowL1 mem pa pb (m + 2) i).memory (m + 2))
      (rowBi mem pb (m + 2) i) pa pb (m + 2) i pdst ret rest hcap hrun hcode hfork
      hnp hact hn32 hi hpb hpbFit)

def gasSteps_mpRowLast (s : State) (mem : ByteArray) (pa pb m i : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : m + 2 ≤ 32) (hi : i + 1 = m + 2)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * (m + 2) ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * (m + 2) ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * (m + 2)))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * (m + 2)))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * (m + 2) - 32)) :
    Challenge.EvmProof.GasSteps
      (mpOutState s mem pa pb (m + 2) i pdst ret rest)
      (mpCsubState s (rowMem mem pa pb (m + 2) i) pdst ret rest) :=
  (gasSteps_mpRowToTail s mem pa pb m i pdst ret rest hcap hrun hcode hfork hnp
      hact hn32 (by omega) hpa hpaFit hpb hpbFit hs32 htl hml).trans <|
  (gasSteps_mpTailLast s (rowL2 mem pa pb (m + 2) i).memory
      (UInt256.ofNat (ptrAt (32 * (m + 2) - 64) (m + 1)))
      (UInt256.ofNat (ptrAt (8192 + 32 * (m + 2)) (m + 1)))
      (rowL2 mem pa pb (m + 2) i).carry
      (rowMu (rowL1 mem pa pb (m + 2) i).memory (m + 2))
      (rowBi mem pb (m + 2) i) pa pb (m + 2) i pdst ret rest hcap hrun hcode hfork
      hnp hact hn32 hi hpb hpbFit).trans
  (gasSteps_mpExit s (rowMem mem pa pb (m + 2) i)
      (UInt256.ofNat (ptrAt (pb + 32 * (m + 2) - 32) (i + 1))) pa pb pdst ret rest
      hcap hrun hcode hfork hnp)

def gasSteps_mpRows (s : State) (memory : ByteArray) (pa pb m : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : m + 2 ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * (m + 2) ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * (m + 2) ≤ 9472)
    (hs32 : MachineState.readWord memory 9344 = UInt256.ofNat (32 * (m + 2)))
    (htl : MachineState.readWord memory 9440 = UInt256.ofNat (8224 + 32 * (m + 2)))
    (hml : MachineState.readWord memory 9408 =
      UInt256.ofNat (32 * (m + 2) - 32)) :
    Challenge.EvmProof.GasSteps
      (mpOutState s memory pa pb (m + 2) 0 pdst ret rest)
      (mpOutState s (rowsMem memory pa pb (m + 2) (m + 1)) pa pb (m + 2) (m + 1)
        pdst ret rest) :=
  Challenge.EvmProof.GasSteps.iterateBounded
    (I := fun i =>
      mpOutState s (rowsMem memory pa pb (m + 2) i) pa pb (m + 2) i pdst ret rest)
    (m + 1)
    (fun i hi => gasSteps_mpRowNext s (rowsMem memory pa pb (m + 2) i) pa pb m i
      pdst ret rest hcap hrun hcode hfork hnp hact hn32 (by omega) hpa hpaFit hpb
      hpbFit
      ((readWord_rowsMem memory pa pb (m + 2) 9344 hn32 (by omega) i).trans hs32)
      ((readWord_rowsMem memory pa pb (m + 2) 9440 hn32 (by omega) i).trans htl)
      ((readWord_rowsMem memory pa pb (m + 2) 9408 hn32 (by omega) i).trans hml))

/-! ## The whole subroutine, up to the tail call into `CSUB` -/

def gasSteps_monproToCsub (s : State) (mem : ByteArray) (pa pb m : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : m + 2 ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * (m + 2) ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * (m + 2) ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * (m + 2)))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * (m + 2)))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * (m + 2) - 32)) :
    Challenge.EvmProof.GasSteps
      (mpEntryState s mem pa pb pdst ret rest)
      (mpCsubState s
        (rowsMem (mpZeroed s mem (m + 2)) pa pb (m + 2) (m + 2)) pdst ret rest) :=
  (gasSteps_mpEntry s mem pa pb (m + 2) pdst ret rest hcap hrun hcode hfork hnp
      hact (by omega) hn32 hpa hpaFit hpb hpbFit hcds hs32).trans <|
  (gasSteps_mpRows s (mpZeroed s mem (m + 2)) pa pb m pdst ret rest hcap hrun
      hcode hfork hnp hact hn32 hpa hpaFit hpb hpbFit
      ((readWord_mpZeroed s mem (m + 2) 9344 hn32 (by omega)).trans hs32)
      ((readWord_mpZeroed s mem (m + 2) 9440 hn32 (by omega)).trans htl)
      ((readWord_mpZeroed s mem (m + 2) 9408 hn32 (by omega)).trans hml)).trans
  (gasSteps_mpRowLast s (rowsMem (mpZeroed s mem (m + 2)) pa pb (m + 2) (m + 1))
      pa pb m (m + 1) pdst ret rest hcap hrun hcode hfork hnp hact hn32 rfl hpa
      hpaFit hpb hpbFit
      ((readWord_rowsMem (mpZeroed s mem (m + 2)) pa pb (m + 2) 9344 hn32
          (by omega) (m + 1)).trans
        ((readWord_mpZeroed s mem (m + 2) 9344 hn32 (by omega)).trans hs32))
      ((readWord_rowsMem (mpZeroed s mem (m + 2)) pa pb (m + 2) 9440 hn32
          (by omega) (m + 1)).trans
        ((readWord_mpZeroed s mem (m + 2) 9440 hn32 (by omega)).trans htl))
      ((readWord_rowsMem (mpZeroed s mem (m + 2)) pa pb (m + 2) 9408 hn32
          (by omega) (m + 1)).trans
        ((readWord_mpZeroed s mem (m + 2) 9408 hn32 (by omega)).trans hml)))

/-! ## Preservation of the named memory blocks

Every named block of the memory map except the CIOS scratch area lies below
`T_ = 0x2000 = 8192`: `M = 0`, `ACC = 0x400`, `BASE = 0x800`, `ONE = 0xC00`,
`R1 = 0x1000`, `CC = 0x1400`, `RR = 0x1800`, `SUBB = 0x1C00`, each of at most
`32 * 32 = 1024` bytes.  `MONPRO` leaves all of them, and every scratch word at
or above `9280`, untouched. -/

theorem readWord_monpro_preserved (s : State) (memory : ByteArray)
    (pa pb n i addr : Nat) (hn : n ≤ 32)
    (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (rowsMem (mpZeroed s memory n) pa pb n i) addr =
      MachineState.readWord memory addr := by
  rw [readWord_rowsMem _ _ _ _ _ hn haddr i, readWord_mpZeroed _ _ _ _ hn haddr]

theorem fastRepresents_monpro_preserved (s : State) (memory : ByteArray)
    (pa pb n i ptr count value : Nat) (hn : n ≤ 32)
    (hfit : ptr + 32 * count ≤ 8192)
    (hrep : Model.FastRepresents memory ptr count value) :
    Model.FastRepresents (rowsMem (mpZeroed s memory n) pa pb n i) ptr count value := by
  refine (Model.fastRepresents_congr
    (a := memory) (b := rowsMem (mpZeroed s memory n) pa pb n i) ?_ value).1 hrep
  intro j hj
  rw [readWord_monpro_preserved s memory pa pb n i (ptr + 32 * j) hn (by omega)]

/-! ## The subroutine trace

`MONPRO` is entered at pc 1939 with stack `[pa, pb, pd, ret]` and tail-calls
`CSUB` at pc 2642 with stack `[pd, ret]`; `CSUB` (proved in `Fast.Csub`) copies
the reduced product to `pd` and returns to `ret`.  The trace below therefore
ends exactly at the `CSUB` entry state. -/

def gasSteps_monpro (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32)) :
    Challenge.EvmProof.GasSteps
      (mpEntryState s mem pa pb pdst ret rest)
      (mpCsubState s (rowsMem (mpZeroed s mem n) pa pb n n) pdst ret rest) := by
  cases n with
  | zero => exact absurd hn (by omega)
  | succ k =>
    cases k with
    | zero => exact absurd hn (by omega)
    | succ m =>
      exact gasSteps_monproToCsub s mem pa pb m pdst ret rest hcap hrun hcode hfork
        hnp hact hn32 hpa hpaFit hpb hpbFit hcds hs32 htl hml

/-! ## The limbs of the CIOS accumulator

`t[k]` lives at `tAddr n k = 8256 + 32 * (n - 1 - k)`.  The source blocks at
`pa`, `pb` and the modulus at `0` all lie below `T_ = 8192`, so no limb store
of `MONPRO` disturbs them. -/

theorem radix_eq : Limbs.radix = 2 ^ 256 := rfl

/-- The address of `t[k]`, counted from the least significant limb. -/
def tAddr (n k : Nat) : Nat := 8256 + 32 * (n - 1 - k)

/-- The value of the first `j` limbs produced by `f`, in radix `2 ^ 256`. -/
def limbSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => limbSum f j + f j * Limbs.radix ^ j

@[simp] theorem limbSum_zero (f : Nat → Nat) : limbSum f 0 = 0 := rfl

theorem limbSum_succ (f : Nat → Nat) (j : Nat) :
    limbSum f (j + 1) = limbSum f j + f j * Limbs.radix ^ j := rfl

theorem limbSum_congr {f g : Nat → Nat} (j : Nat) (h : ∀ k, k < j → f k = g k) :
    limbSum f j = limbSum g j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [limbSum_succ, limbSum_succ, ih (fun k hk => h k (by omega)),
        h j (by omega)]

/-- Limb `k` of `t` is untouched until step `k` of the first loop. -/
theorem readWord_l1Step_keep (mem : ByteArray) (bi : UInt256) (pa n k : Nat)
    (hkn : k < n) : ∀ j, j ≤ k →
    MachineState.readWord (l1Step mem bi pa n j).memory (tAddr n k) =
      MachineState.readWord mem (tAddr n k) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      simp only [l1Step]
      rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih (by omega)
      · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
        simp only [tAddr]
        omega

/-- The source blocks below `T_` are untouched by the first loop. -/
theorem readWord_l1Step_src (mem : ByteArray) (bi : UInt256) (pa n j addr : Nat)
    (hn : n ≤ 32) (haddr : addr + 32 ≤ 8192) :
    MachineState.readWord (l1Step mem bi pa n j).memory addr =
      MachineState.readWord mem addr :=
  readWord_l1Step mem bi pa n addr j hn (Or.inl haddr)

/-- The limb the first loop stores at step `k`. -/
def l1Val (mem : ByteArray) (bi : UInt256) (pa n k : Nat) : UInt256 :=
  macSum (MachineState.readWord mem (pa + 32 * (n - 1 - k))) bi
    (MachineState.readWord mem (tAddr n k)) (l1Step mem bi pa n k).carry

theorem l1Step_succ_carry (mem : ByteArray) (bi : UInt256) (pa n j : Nat)
    (hn : n ≤ 32) (hj : j < n) (hpaFit : pa + 32 * n ≤ 8192) :
    (l1Step mem bi pa n (j + 1)).carry =
      macCarry (MachineState.readWord mem (pa + 32 * (n - 1 - j))) bi
        (MachineState.readWord mem (tAddr n j)) (l1Step mem bi pa n j).carry := by
  have hkeep : MachineState.readWord (l1Step mem bi pa n j).memory
      (8256 + 32 * (n - 1 - j)) =
      MachineState.readWord mem (8256 + 32 * (n - 1 - j)) :=
    readWord_l1Step_keep mem bi pa n j hj j (Nat.le_refl j)
  simp only [l1Step, tAddr]
  rw [readWord_l1Step_src mem bi pa n j (pa + 32 * (n - 1 - j)) hn (by omega), hkeep]

theorem l1Step_succ_write (mem : ByteArray) (bi : UInt256) (pa n j : Nat)
    (hn : n ≤ 32) (hj : j < n) (hpaFit : pa + 32 * n ≤ 8192) :
    (l1Step mem bi pa n (j + 1)).memory =
      MachineState.writeBytes (l1Step mem bi pa n j).memory
        (Data.Bytes.natToBytesPadded (l1Val mem bi pa n j).toNat 32) (tAddr n j) := by
  have hkeep : MachineState.readWord (l1Step mem bi pa n j).memory
      (8256 + 32 * (n - 1 - j)) =
      MachineState.readWord mem (8256 + 32 * (n - 1 - j)) :=
    readWord_l1Step_keep mem bi pa n j hj j (Nat.le_refl j)
  simp only [l1Step, l1Val, tAddr]
  rw [readWord_l1Step_src mem bi pa n j (pa + 32 * (n - 1 - j)) hn (by omega), hkeep]

/-- After step `j`, limb `k < j` holds the value the loop stored. -/
theorem readWord_l1Step_val (mem : ByteArray) (bi : UInt256) (pa n k : Nat)
    (hn : n ≤ 32) (hkn : k < n) (hpaFit : pa + 32 * n ≤ 8192) : ∀ j, k < j → j ≤ n →
    MachineState.readWord (l1Step mem bi pa n j).memory (tAddr n k) =
      l1Val mem bi pa n k := by
  intro j
  induction j with
  | zero => intro h; exact absurd h (Nat.not_lt_zero k)
  | succ j ih =>
      intro hkj hjn
      rw [l1Step_succ_write mem bi pa n j hn (by omega) hpaFit]
      rcases Nat.lt_or_ge k j with hlt | hge
      · rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
        · exact ih hlt (by omega)
        · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
          simp only [tAddr]
          omega
      · have hkeq : k = j := by omega
        subst hkeq
        exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

/-! ## The invariant of the first limb loop -/

private theorem mac_step_alg {S T' A' L C B Wt Wa Bi R Rad : Nat}
    (hmac : B * Rad + L = Wt + Wa * Bi + C)
    (hih : S + C * R = T' + Bi * A') :
    S + L * R + B * (R * Rad) = T' + Wt * R + Bi * (A' + Wa * R) := by
  have h1 : S + L * R + B * (R * Rad) = S + (B * Rad + L) * R := by ring
  rw [h1, hmac]
  have h2 : S + (Wt + Wa * Bi + C) * R = S + C * R + (Wt + Wa * Bi) * R := by ring
  rw [h2, hih]
  ring

/-- `I_L1(j)`: after `j` steps the loop has produced limbs `t'[0..j-1]` and a
carry `C` with
`Σ_{k<j} t'[k] rad^k + C rad^j = Σ_{k<j} t[k] rad^k + b[i] Σ_{k<j} a[k] rad^k`. -/
theorem l1_invariant (mem : ByteArray) (bi : UInt256) (pa n : Nat)
    (hn : n ≤ 32) (hpaFit : pa + 32 * n ≤ 8192) : ∀ j, j ≤ n →
    limbSum (fun k => (l1Val mem bi pa n k).toNat) j +
        (l1Step mem bi pa n j).carry.toNat * Limbs.radix ^ j =
      limbSum (fun k => (MachineState.readWord mem (tAddr n k)).toNat) j +
        bi.toNat * limbSum
          (fun k => (MachineState.readWord mem (pa + 32 * (n - 1 - k))).toNat) j := by
  intro j
  induction j with
  | zero =>
      intro _
      simp [limbSum, l1Step, Challenge.EvmProof.Word.word_toNat_ofNat]
  | succ j ih =>
      intro hjn
      have hj : j < n := by omega
      have hih := ih (Nat.le_of_succ_le hjn)
      have hmac := macSpec (MachineState.readWord mem (pa + 32 * (n - 1 - j))) bi
        (MachineState.readWord mem (tAddr n j)) (l1Step mem bi pa n j).carry
      rw [limbSum_succ, limbSum_succ, limbSum_succ,
        l1Step_succ_carry mem bi pa n j hn hj hpaFit, pow_succ]
      simp only [l1Val]
      exact mac_step_alg hmac hih

/-! ## The limbs of the second limb loop

Step `k` reads `m[k+1]` at `32 * (n - 2 - k)` and `t[k+1]` at
`8256 + 32 * (n - 2 - k)`, and stores into `t[k]` at `tAddr n k`. -/

/-- Nothing below `TS = 8256` is written by the first loop. -/
theorem readWord_l1Step_low (mem : ByteArray) (bi : UInt256) (pa n addr j : Nat)
    (haddr : addr + 32 ≤ 8256) :
    MachineState.readWord (l1Step mem bi pa n j).memory addr =
      MachineState.readWord mem addr := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [l1Step]
      rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih
      · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
        omega

/-- Nothing below `TS = 8256` is written by the second loop. -/
theorem readWord_l2Step_low (mem : ByteArray) (mu c0 : UInt256) (n addr k : Nat)
    (haddr : addr + 32 ≤ 8256) :
    MachineState.readWord (l2Step mem mu c0 n k).memory addr =
      MachineState.readWord mem addr := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [l2Step]
      rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih
      · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
        omega

/-- Limb `k + 1` of `t` is untouched until step `k + 1` of the second loop. -/
theorem readWord_l2Step_keep (mem : ByteArray) (mu c0 : UInt256) (n k : Nat)
    (hkn : k + 1 < n) : ∀ j, j ≤ k →
    MachineState.readWord (l2Step mem mu c0 n j).memory (8256 + 32 * (n - 2 - k)) =
      MachineState.readWord mem (8256 + 32 * (n - 2 - k)) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      simp only [l2Step]
      rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih (by omega)
      · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
        omega

/-- The limb the second loop stores at step `k`. -/
def l2Val (mem : ByteArray) (mu c0 : UInt256) (n k : Nat) : UInt256 :=
  macSum (MachineState.readWord mem (32 * (n - 2 - k))) mu
    (MachineState.readWord mem (8256 + 32 * (n - 2 - k))) (l2Step mem mu c0 n k).carry

theorem l2Step_succ_carry (mem : ByteArray) (mu c0 : UInt256) (n k : Nat)
    (hn : n ≤ 32) (hk : k + 1 < n) :
    (l2Step mem mu c0 n (k + 1)).carry =
      macCarry (MachineState.readWord mem (32 * (n - 2 - k))) mu
        (MachineState.readWord mem (8256 + 32 * (n - 2 - k)))
        (l2Step mem mu c0 n k).carry := by
  simp only [l2Step]
  rw [readWord_l2Step_low mem mu c0 n (32 * (n - 2 - k)) k (by omega),
    readWord_l2Step_keep mem mu c0 n k hk k (Nat.le_refl k)]

theorem l2Step_succ_write (mem : ByteArray) (mu c0 : UInt256) (n k : Nat)
    (hn : n ≤ 32) (hk : k + 1 < n) :
    (l2Step mem mu c0 n (k + 1)).memory =
      MachineState.writeBytes (l2Step mem mu c0 n k).memory
        (Data.Bytes.natToBytesPadded (l2Val mem mu c0 n k).toNat 32) (tAddr n k) := by
  simp only [l2Step, l2Val, tAddr]
  rw [readWord_l2Step_low mem mu c0 n (32 * (n - 2 - k)) k (by omega),
    readWord_l2Step_keep mem mu c0 n k hk k (Nat.le_refl k)]

/-- After step `j`, limb `k < j` holds the value the second loop stored. -/
theorem readWord_l2Step_val (mem : ByteArray) (mu c0 : UInt256) (n k : Nat)
    (hn : n ≤ 32) (hkn : k + 1 < n) : ∀ j, k < j → j + 1 ≤ n →
    MachineState.readWord (l2Step mem mu c0 n j).memory (tAddr n k) =
      l2Val mem mu c0 n k := by
  intro j
  induction j with
  | zero => intro h; exact absurd h (Nat.not_lt_zero k)
  | succ j ih =>
      intro hkj hjn
      rw [l2Step_succ_write mem mu c0 n j hn (by omega)]
      rcases Nat.lt_or_ge k j with hlt | hge
      · rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
        · exact ih hlt (by omega)
        · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
          simp only [tAddr]
          omega
      · have hkeq : k = j := by omega
        subst hkeq
        exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

/-! ## The invariant of the second limb loop -/

private theorem mac_step_alg2 {S T' A' L C B Wt Wa Bi R Rad C0 : Nat}
    (hmac : B * Rad + L = Wt + Wa * Bi + C)
    (hih : S + C * R = C0 + (T' + Bi * A')) :
    S + L * R + B * (R * Rad) = C0 + (T' + Wt * R + Bi * (A' + Wa * R)) := by
  have h1 : S + L * R + B * (R * Rad) = S + (B * Rad + L) * R := by ring
  rw [h1, hmac]
  have h2 : S + (Wt + Wa * Bi + C) * R = S + C * R + (Wt + Wa * Bi) * R := by ring
  rw [h2, hih]
  ring

/-- `I_L2(j)`: after `j` steps of the second loop,
`Σ_{k<j} t''[k] rad^k + C rad^j = C₀ + Σ_{k<j} t[k+1] rad^k + mu Σ_{k<j} m[k+1] rad^k`. -/
theorem l2_invariant (mem : ByteArray) (mu c0 : UInt256) (n : Nat)
    (hn : n ≤ 32) : ∀ j, j + 1 ≤ n →
    limbSum (fun k => (l2Val mem mu c0 n k).toNat) j +
        (l2Step mem mu c0 n j).carry.toNat * Limbs.radix ^ j =
      c0.toNat +
        (limbSum
            (fun k => (MachineState.readWord mem (8256 + 32 * (n - 2 - k))).toNat) j +
          mu.toNat *
            limbSum (fun k => (MachineState.readWord mem (32 * (n - 2 - k))).toNat) j) := by
  intro j
  induction j with
  | zero => intro _; simp [limbSum, l2Step]
  | succ j ih =>
      intro hjn
      have hih := ih (by omega)
      have hmac := macSpec (MachineState.readWord mem (32 * (n - 2 - j))) mu
        (MachineState.readWord mem (8256 + 32 * (n - 2 - j)))
        (l2Step mem mu c0 n j).carry
      rw [limbSum_succ, limbSum_succ, limbSum_succ,
        l2Step_succ_carry mem mu c0 n j hn (by omega), pow_succ]
      simp only [l2Val]
      exact mac_step_alg2 hmac hih

/-! ## From limb sums to represented values -/

theorem limbSum_digits (value : Nat) : ∀ j,
    limbSum (fun k => value / Limbs.radix ^ k % Limbs.radix) j =
      value % Limbs.radix ^ j := by
  intro j
  induction j with
  | zero => rw [limbSum_zero, pow_zero, Nat.mod_one]
  | succ j ih =>
      have hdvd : Limbs.radix ^ j ∣ Limbs.radix ^ j * Limbs.radix := Dvd.intro _ rfl
      have hmod : value % (Limbs.radix ^ j * Limbs.radix) % Limbs.radix ^ j =
          value % Limbs.radix ^ j := Nat.mod_mod_of_dvd value hdvd
      have hdiv : value % (Limbs.radix ^ j * Limbs.radix) / Limbs.radix ^ j =
          value / Limbs.radix ^ j % Limbs.radix :=
        Nat.mod_mul_right_div_self value (Limbs.radix ^ j) Limbs.radix
      have hsplit := Nat.div_add_mod (value % (Limbs.radix ^ j * Limbs.radix))
        (Limbs.radix ^ j)
      rw [hmod, hdiv] at hsplit
      rw [limbSum_succ, ih, pow_succ,
        Nat.mul_comm (value / Limbs.radix ^ j % Limbs.radix) (Limbs.radix ^ j),
        Nat.add_comm (value % Limbs.radix ^ j)
          (Limbs.radix ^ j * (value / Limbs.radix ^ j % Limbs.radix))]
      exact hsplit

theorem limbSum_fastRepresents {mem : ByteArray} {ptr count value : Nat}
    (hrep : Model.FastRepresents mem ptr count value) :
    limbSum (fun k => (MachineState.readWord mem (ptr + 32 * (count - 1 - k))).toNat)
        count = value := by
  rw [limbSum_congr count
      (g := fun k => value / Limbs.radix ^ k % Limbs.radix)
      (fun k hk => Model.readLimb_of_fastRepresents hrep hk),
    limbSum_digits value count,
    Nat.mod_eq_of_lt (Model.fastRepresents_lt hrep)]

/-- The first loop of a row computes `t_low + b[i] * a` exactly:
`Σ_{k<n} t'[k] rad^k + C rad^n = t_low + b[i] * a`. -/
theorem l1_row (mem : ByteArray) (bi : UInt256) (pa n tlow a : Nat)
    (hn : n ≤ 32) (hpaFit : pa + 32 * n ≤ 8192)
    (hta : Model.FastRepresents mem pa n a)
    (htt : Model.FastRepresents mem 8256 n tlow) :
    limbSum (fun k => (l1Val mem bi pa n k).toNat) n +
        (l1Step mem bi pa n n).carry.toNat * Limbs.radix ^ n =
      tlow + bi.toNat * a := by
  have h := l1_invariant mem bi pa n hn hpaFit n (Nat.le_refl n)
  simp only [tAddr] at h
  rw [limbSum_fastRepresents hta, limbSum_fastRepresents htt] at h
  exact h

/-! ## The row middle: `t[n] + C` and the `mu` choice -/

/-- A single `ADD` with its carry-out flag. -/
theorem add_carry_split (x y : UInt256) :
    (UInt256.lt (x + y) y).toNat * 2 ^ 256 + (x + y).toNat = x.toNat + y.toNat := by
  have h := carry_split y.toNat x.toNat (word_lt_size y) (word_lt_size x)
  rw [Nat.add_comm y.toNat x.toNat] at h
  rw [word_toNat_lt', Challenge.EvmProof.Word.word_toNat_add x y]
  exact h.symm

private theorem mod_split_two {x : Nat} (hx : x < 2 ^ 256 + 2 ^ 256)
    (h : x % 2 ^ 256 = 0) : x = 0 ∨ x = 2 ^ 256 := by
  rcases Nat.lt_or_ge x (2 ^ 256) with hlt | hge
  · left
    rwa [Nat.mod_eq_of_lt hlt] at h
  · right
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h
    omega

private theorem c0_final {t0 lo hi : Nat} (hlo : lo < 2 ^ 256) (ht0 : t0 < 2 ^ 256)
    (hhi : hi < 2 ^ 256 - 1) (hsum : t0 + lo = 0 ∨ t0 + lo = 2 ^ 256) :
    ((if lo = 0 then 0 else 1) + hi) % 2 ^ 256 * 2 ^ 256 =
      t0 + (hi * 2 ^ 256 + lo) := by
  rcases hsum with h | h
  · rw [if_pos (by omega), Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [if_neg (by omega), Nat.mod_eq_of_lt (by omega)]
    have hexp : (1 + hi) * 2 ^ 256 = 2 ^ 256 + hi * 2 ^ 256 := by ring
    omega

/-- `mu = minv * t[0]` makes the row sum divisible by the radix, and the
carry the code computes is exactly the quotient:
`t[0] + m[0] * mu = C₀ * radix`. -/
theorem c0_spec (m0 minv t0 : UInt256)
    (hminv : (m0.toNat * minv.toNat + 1) % 2 ^ 256 = 0) :
    (UInt256.isZero (UInt256.isZero (m0 * (minv * t0))) +
          mulHi m0 (minv * t0)).toNat * 2 ^ 256 =
      t0.toNat + m0.toNat * (minv * t0).toNat := by
  have hprod := mulHi_spec m0 (minv * t0)
  have hhi : (mulHi m0 (minv * t0)).toNat < 2 ^ 256 - 1 := by
    rw [mulHi_toNat]
    exact high_lt (by norm_num) (word_lt_size m0) (word_lt_size (minv * t0))
  have hlolt : (m0 * (minv * t0)).toNat < 2 ^ 256 := word_lt_size _
  have ht0lt : t0.toNat < 2 ^ 256 := word_lt_size _
  have hmu : (minv * t0).toNat ≡ minv.toNat * t0.toNat [MOD 2 ^ 256] := by
    rw [word_toNat_mul minv t0]
    exact Nat.mod_modEq _ _
  have e1 : t0.toNat + m0.toNat * (minv * t0).toNat ≡
      t0.toNat * (m0.toNat * minv.toNat + 1) [MOD 2 ^ 256] := by
    calc t0.toNat + m0.toNat * (minv * t0).toNat
        ≡ t0.toNat + m0.toNat * (minv.toNat * t0.toNat) [MOD 2 ^ 256] :=
          Nat.ModEq.add_left _ (hmu.mul_left m0.toNat)
      _ = t0.toNat * (m0.toNat * minv.toNat + 1) := by ring
  have e2 : t0.toNat * (m0.toNat * minv.toNat + 1) ≡ 0 [MOD 2 ^ 256] := by
    have hz : m0.toNat * minv.toNat + 1 ≡ 0 [MOD 2 ^ 256] := by
      unfold Nat.ModEq
      rw [hminv, Nat.zero_mod]
    simpa using hz.mul_left t0.toNat
  have hdvd : (t0.toNat + m0.toNat * (minv * t0).toNat) % 2 ^ 256 = 0 := by
    have h := e1.trans e2
    unfold Nat.ModEq at h
    rw [Nat.zero_mod] at h
    exact h
  have hA : (UInt256.isZero (UInt256.isZero (m0 * (minv * t0)))).toNat =
      if (m0 * (minv * t0)).toNat = 0 then 0 else 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_isZero (UInt256.isZero (m0 * (minv * t0))),
      Challenge.EvmProof.Word.word_toNat_isZero (m0 * (minv * t0))]
    by_cases h : (m0 * (minv * t0)).toNat = 0 <;> simp [h]
  rw [← hprod] at hdvd ⊢
  have hmod : (t0.toNat + (m0 * (minv * t0)).toNat) % 2 ^ 256 = 0 := by
    have hrw : t0.toNat +
          ((mulHi m0 (minv * t0)).toNat * 2 ^ 256 + (m0 * (minv * t0)).toNat) =
        t0.toNat + (m0 * (minv * t0)).toNat +
          (mulHi m0 (minv * t0)).toNat * 2 ^ 256 := by ring
    rw [hrw, Nat.add_mul_mod_self_right] at hdvd
    exact hdvd
  have hsum := mod_split_two (Nat.add_lt_add ht0lt hlolt) hmod
  rw [Challenge.EvmProof.Word.word_toNat_add, hA]
  exact c0_final hlolt ht0lt hhi hsum

/-! ## The tail call into `CSUB`

`MONPRO` enters `CSUB` at pc 2642 with stack `[pd, ret]`, `t[n]` at
`TN = 8224` and `t_low` in the `n`-limb block at `TS = 8256` — exactly
`Csub.csEntryState`'s shape.  `Csub.gasSteps_csub` then reduces `t` modulo the
modulus, copies the result to `pd` and jumps to `ret`. -/

/-- `limbSum` over the words of a block is `Csub.lowValue`, so the loop
invariants above line up with the `CSUB` side. -/
theorem limbSum_eq_lowValue (memory : ByteArray) (ptr n j : Nat) :
    limbSum (fun k => (MachineState.readWord memory (ptr + 32 * (n - 1 - k))).toNat) j =
      Csub.lowValue memory ptr n j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [limbSum_succ, Csub.lowValue_succ, ih]

/-- The whole `MONPRO` call: from the subroutine entry at pc 1939 with stack
`[pa, pb, pd, ret]` through the `n` CIOS rows and the tail call to `CSUB`, back
to the caller at `ret`.  The single arithmetic side condition `htn` — the CIOS
accumulator's top limb is at most one, which is the `t < 2 m` bound of the row
invariant — is left to the caller. -/
def gasSteps_monproCsub (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32))
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hdstFit : pdst.toNat + 32 * n ≤ 9472)
    (htn : (MachineState.readWord (rowsMem (mpZeroed s mem n) pa pb n n) 8224).toNat
      ≤ 1) :
    Challenge.EvmProof.GasSteps
      (mpEntryState s mem pa pb pdst ret rest)
      (Csub.csReturnedState s (rowsMem (mpZeroed s mem n) pa pb n n) n n pdst ret
        rest) :=
  (gasSteps_monpro s mem pa pb n pdst ret rest hcap hrun hcode hfork hnp hact hn
      hn32 hpa hpaFit hpb hpbFit hcds hs32 htl hml).trans
    (Csub.gasSteps_csub s (rowsMem (mpZeroed s mem n) pa pb n n) n pdst ret rest
      hcap hcode hfork hrun hnp hact hn hn32 hjump
      ((readWord_monpro_preserved s mem pa pb n n 9408 hn32 (by omega)).trans hml)
      ((readWord_monpro_preserved s mem pa pb n n 9440 hn32 (by omega)).trans htl)
      ((Csub.csStep_readWord_disjoint (rowsMem (mpZeroed s mem n) pa pb n n) n 9344
            (by omega) (Or.inr (by omega)) n (Nat.le_refl n)).trans
        ((readWord_monpro_preserved s mem pa pb n n 9344 hn32 (by omega)).trans hs32))
      hdstFit
      (by
        rw [Csub.csStep_readWord_disjoint (rowsMem (mpZeroed s mem n) pa pb n n) n
          8224 (by omega) (Or.inr (by omega)) n (Nat.le_refl n)]
        exact htn))

/-! ## Plumbing for the row equation -/

theorem limbSum_shift (f : Nat → Nat) : ∀ j,
    limbSum (fun k => f (k + 1)) j * Limbs.radix + f 0 = limbSum f (j + 1) := by
  intro j
  induction j with
  | zero => simp [limbSum]
  | succ j ih =>
      rw [limbSum_succ, limbSum_succ (f := f) (j := j + 1)]
      calc (limbSum (fun k => f (k + 1)) j + f (j + 1) * Limbs.radix ^ j) *
              Limbs.radix + f 0
          = (limbSum (fun k => f (k + 1)) j * Limbs.radix + f 0) +
              f (j + 1) * (Limbs.radix ^ j * Limbs.radix) := by ring
        _ = limbSum f (j + 1) + f (j + 1) * (Limbs.radix ^ j * Limbs.radix) := by
              rw [ih]
        _ = limbSum f (j + 1) + f (j + 1) * Limbs.radix ^ (j + 1) := by
              rw [pow_succ]

/-- Reads at or above `TS = 8256` see through the row middle. -/
theorem readWord_midMem_high (mem : ByteArray) (c : UInt256) (r : Nat)
    (hr : 8256 ≤ r) :
    MachineState.readWord (midMem mem c) r = MachineState.readWord mem r :=
  readWord_midMem_peel mem _ _ r (Or.inr hr)

/-- Reads below `T_ = 8192` see through the row middle. -/
theorem readWord_midMem_low' (mem : ByteArray) (c : UInt256) (r : Nat)
    (hr : r + 32 ≤ 8192) :
    MachineState.readWord (midMem mem c) r = MachineState.readWord mem r :=
  readWord_midMem_peel mem _ _ r (Or.inl hr)

/-- The two `MSTORE`s of the row tail land at `8256` and `8224`. -/
theorem readWord_tailMem_peel (mem : ByteArray) (v w r : Nat)
    (hr : r + 32 ≤ 8224 ∨ 8288 ≤ r) :
    MachineState.readWord
        (MachineState.writeBytes
          (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 8256)
          (Data.Bytes.natToBytesPadded w 32) 8224) r =
      MachineState.readWord mem r := by
  have h1 : MachineState.readWord
      (MachineState.writeBytes
        (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 8256)
        (Data.Bytes.natToBytesPadded w 32) 8224) r =
      MachineState.readWord
        (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 8256) r := by
    apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  have h2 : MachineState.readWord
      (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 8256) r =
      MachineState.readWord mem r := by
    apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  rw [h1, h2]

theorem readWord_tailMem_high (mem : ByteArray) (c : UInt256) (r : Nat)
    (hr : 8288 ≤ r) :
    MachineState.readWord (tailMem mem c) r = MachineState.readWord mem r :=
  readWord_tailMem_peel mem _ _ r (Or.inr hr)

/-- The row tail stores `t[n] + C` into `t[n-1]` at `TS`. -/
theorem readWord_tailMem_ts (mem : ByteArray) (c : UInt256) :
    MachineState.readWord (tailMem mem c) 8256 =
      MachineState.readWord mem 8224 + c := by
  have h1 : MachineState.readWord (tailMem mem c) 8256 =
      MachineState.readWord (tailMem1 mem c) 8256 := by
    apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  simp only [h1, tailMem1]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

/-- The row tail stores `t[n+1] + carry` into `t[n]` at `TN`. -/
theorem readWord_tailMem_tn (mem : ByteArray) (c : UInt256) :
    MachineState.readWord (tailMem mem c) 8224 =
      MachineState.readWord mem 8192 +
        UInt256.lt (MachineState.readWord mem 8224 + c) c := by
  have hlow : MachineState.readWord (tailMem1 mem c) 8192 =
      MachineState.readWord mem 8192 := by
    apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  simp only [tailMem]
  rw [Challenge.EvmProof.Memory.readWord_writeWord, hlow]

/-- The row middle stores `t[n] + C` at `TN` and the carry at `T_`. -/
theorem readWord_midMem_tn (mem : ByteArray) (c : UInt256) :
    MachineState.readWord (midMem mem c) 8224 =
      MachineState.readWord mem 8224 + c := by
  have h1 : MachineState.readWord (midMem mem c) 8224 =
      MachineState.readWord (midMem1 mem c) 8224 := by
    apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  simp only [h1, midMem1]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

theorem readWord_midMem_tnp (mem : ByteArray) (c : UInt256) :
    MachineState.readWord (midMem mem c) 8192 =
      UInt256.lt (MachineState.readWord mem 8224 + c) c := by
  simp only [midMem]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

/-! ## The contents of the `t` block after one row -/

theorem rowL1_def (mem : ByteArray) (pa pb n i : Nat) :
    rowL1 mem pa pb n i = l1Step mem (rowBi mem pb n i) pa n n := rfl

theorem rowMid_def (mem : ByteArray) (pa pb n i : Nat) :
    rowMid mem pa pb n i =
      midMem (rowL1 mem pa pb n i).memory (rowL1 mem pa pb n i).carry := rfl

theorem rowL2_def (mem : ByteArray) (pa pb n i : Nat) :
    rowL2 mem pa pb n i =
      l2Step (rowMid mem pa pb n i) (rowMu (rowL1 mem pa pb n i).memory n)
        (rowC0 (rowL1 mem pa pb n i).memory n) n (n - 1) := rfl

theorem rowMem_def (mem : ByteArray) (pa pb n i : Nat) :
    rowMem mem pa pb n i =
      tailMem (rowL2 mem pa pb n i).memory (rowL2 mem pa pb n i).carry := rfl

/-- Limbs `0 .. n-2` of the new `t` are what the second loop stored. -/
theorem readWord_rowMem_limb (mem : ByteArray) (pa pb n i k : Nat)
    (hn32 : n ≤ 32) (hk : k + 2 ≤ n) :
    MachineState.readWord (rowMem mem pa pb n i) (tAddr n k) =
      l2Val (rowMid mem pa pb n i) (rowMu (rowL1 mem pa pb n i).memory n)
        (rowC0 (rowL1 mem pa pb n i).memory n) n k := by
  rw [rowMem_def, readWord_tailMem_high _ _ _ (by simp only [tAddr]; omega),
    rowL2_def]
  exact readWord_l2Step_val _ _ _ n k hn32 (by omega) (n - 1) (by omega) (by omega)

/-- Limb `n-1` of the new `t` is `t[n] + C`. -/
theorem readWord_rowMem_top (mem : ByteArray) (pa pb n i : Nat) :
    MachineState.readWord (rowMem mem pa pb n i) 8256 =
      MachineState.readWord (rowL2 mem pa pb n i).memory 8224 +
        (rowL2 mem pa pb n i).carry := by
  rw [rowMem_def, readWord_tailMem_ts]

/-- The new `t[n]` is `t[n+1] + carry`. -/
theorem readWord_rowMem_tn (mem : ByteArray) (pa pb n i : Nat) :
    MachineState.readWord (rowMem mem pa pb n i) 8224 =
      MachineState.readWord (rowL2 mem pa pb n i).memory 8192 +
        UInt256.lt (MachineState.readWord (rowL2 mem pa pb n i).memory 8224 +
          (rowL2 mem pa pb n i).carry) (rowL2 mem pa pb n i).carry := by
  rw [rowMem_def, readWord_tailMem_tn]

theorem lowValue_rowMem (mem : ByteArray) (pa pb p i : Nat) (hn32 : p + 2 ≤ 32) :
    Csub.lowValue (rowMem mem pa pb (p + 2) i) 8256 (p + 2) (p + 2) =
      limbSum (fun k => (l2Val (rowMid mem pa pb (p + 2) i)
          (rowMu (rowL1 mem pa pb (p + 2) i).memory (p + 2))
          (rowC0 (rowL1 mem pa pb (p + 2) i).memory (p + 2)) (p + 2) k).toNat)
          (p + 1) +
        (MachineState.readWord (rowMem mem pa pb (p + 2) i) 8256).toNat *
          Limbs.radix ^ (p + 1) := by
  rw [← limbSum_eq_lowValue, limbSum_succ]
  have hlast : (MachineState.readWord (rowMem mem pa pb (p + 2) i)
      (8256 + 32 * (p + 2 - 1 - (p + 1)))).toNat =
      (MachineState.readWord (rowMem mem pa pb (p + 2) i) 8256).toNat := by
    have h0 : 8256 + 32 * (p + 2 - 1 - (p + 1)) = 8256 := by omega
    rw [h0]
  rw [hlast]
  congr 1
  apply limbSum_congr
  intro k hk
  have h := readWord_rowMem_limb mem pa pb (p + 2) i k hn32 (by omega)
  simp only [tAddr] at h
  have haddr : 8256 + 32 * (p + 2 - 1 - k) = 8256 + 32 * (p + 2 - 1 - k) := rfl
  rw [haddr, h]

/-! ## The row equation -/

private theorem row_alg {R P tn Cn u cu Cp v cv c0 mu m0 l0 S2 St Sm L1sum mm tlow
    a bi : Nat}
    (hA : cu * R + u = tn + Cn)
    (hB : cv * R + v = u + Cp)
    (hC : c0 * R = l0 + m0 * mu)
    (hD : S2 + Cp * P = c0 + (St + mu * Sm))
    (hE : St * R + l0 = L1sum)
    (hF : Sm * R + m0 = mm)
    (hG : L1sum + Cn * (P * R) = tlow + bi * a) :
    ((cu + cv) * (P * R) + (S2 + v * P)) * R =
      tn * (P * R) + tlow + a * bi + mu * mm := by
  calc ((cu + cv) * (P * R) + (S2 + v * P)) * R
      = cu * R * (P * R) + (cv * R + v) * (P * R) + S2 * R := by ring
    _ = cu * R * (P * R) + (u + Cp) * (P * R) + S2 * R := by rw [hB]
    _ = (cu * R + u) * (P * R) + (S2 + Cp * P) * R := by ring
    _ = (tn + Cn) * (P * R) + (S2 + Cp * P) * R := by rw [hA]
    _ = (tn + Cn) * (P * R) + (c0 + (St + mu * Sm)) * R := by rw [hD]
    _ = (tn + Cn) * (P * R) + (c0 * R + (St * R + mu * (Sm * R))) := by ring
    _ = (tn + Cn) * (P * R) + ((l0 + m0 * mu) + (St * R + mu * (Sm * R))) := by
          rw [hC]
    _ = (tn + Cn) * (P * R) + ((St * R + l0) + mu * (Sm * R + m0)) := by ring
    _ = (tn + Cn) * (P * R) + (L1sum + mu * (Sm * R + m0)) := by rw [hE]
    _ = (tn + Cn) * (P * R) + (L1sum + mu * mm) := by rw [hF]
    _ = tn * (P * R) + (L1sum + Cn * (P * R)) + mu * mm := by ring
    _ = tn * (P * R) + (tlow + bi * a) + mu * mm := by rw [hG]
    _ = tn * (P * R) + tlow + a * bi + mu * mm := by ring

/-- One CIOS row is exact: `t_{i+1} · rad = t_i + a · b[i] + mu · m`. -/
theorem row_equation (mem : ByteArray) (pa pb p i : Nat) (a mm tlow : Nat)
    (hn32 : p + 2 ≤ 32) (hpaFit : pa + 32 * (p + 2) ≤ 8192)
    (ha : Model.FastRepresents mem pa (p + 2) a)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (ht : Model.FastRepresents mem 8256 (p + 2) tlow)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    ((MachineState.readWord (rowMem mem pa pb (p + 2) i) 8224).toNat *
          Limbs.radix ^ (p + 2) +
        Csub.lowValue (rowMem mem pa pb (p + 2) i) 8256 (p + 2) (p + 2)) *
        Limbs.radix =
      (MachineState.readWord mem 8224).toNat * Limbs.radix ^ (p + 2) + tlow +
        a * (rowBi mem pb (p + 2) i).toNat +
        (rowMu (rowL1 mem pa pb (p + 2) i).memory (p + 2)).toNat * mm := by
  have hpow : Limbs.radix ^ (p + 2) = Limbs.radix ^ (p + 1) * Limbs.radix :=
    pow_succ Limbs.radix (p + 1)
  have hA1 : MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory 8224 =
      MachineState.readWord mem 8224 :=
    readWord_l1Step_low mem (rowBi mem pb (p + 2) i) pa (p + 2) 8224 (p + 2) (by omega)
  have hM0 : MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory
      (32 * (p + 2) - 32) = MachineState.readWord mem (32 * (p + 2) - 32) :=
    readWord_l1Step_low mem (rowBi mem pb (p + 2) i) pa (p + 2)
      (32 * (p + 2) - 32) (p + 2) (by omega)
  have hMinvR : MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory 9376 =
      MachineState.readWord mem 9376 :=
    readWord_l1Step mem (rowBi mem pb (p + 2) i) pa (p + 2) 9376 (p + 2) hn32
      (Or.inr (by omega))
  have hT0 : MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory
      (8224 + 32 * (p + 2)) =
      l1Val mem (rowBi mem pb (p + 2) i) pa (p + 2) 0 := by
    have h := readWord_l1Step_val mem (rowBi mem pb (p + 2) i) pa (p + 2) 0 hn32
      (by omega) hpaFit (p + 2) (by omega) (Nat.le_refl _)
    simp only [tAddr] at h
    have haddr : 8256 + 32 * (p + 2 - 1 - 0) = 8224 + 32 * (p + 2) := by omega
    rw [haddr] at h
    exact h
  have hMDtn : MachineState.readWord (rowMid mem pa pb (p + 2) i) 8224 =
      MachineState.readWord mem 8224 + (rowL1 mem pa pb (p + 2) i).carry := by
    rw [rowMid_def, readWord_midMem_tn, hA1]
  have hMDtnp : MachineState.readWord (rowMid mem pa pb (p + 2) i) 8192 =
      UInt256.lt (MachineState.readWord mem 8224 + (rowL1 mem pa pb (p + 2) i).carry)
        (rowL1 mem pa pb (p + 2) i).carry := by
    rw [rowMid_def, readWord_midMem_tnp, hA1]
  have hL2tn : MachineState.readWord (rowL2 mem pa pb (p + 2) i).memory 8224 =
      MachineState.readWord (rowMid mem pa pb (p + 2) i) 8224 :=
    readWord_l2Step_low _ _ _ (p + 2) 8224 (p + 2 - 1) (by omega)
  have hL2tnp : MachineState.readWord (rowL2 mem pa pb (p + 2) i).memory 8192 =
      MachineState.readWord (rowMid mem pa pb (p + 2) i) 8192 :=
    readWord_l2Step_low _ _ _ (p + 2) 8192 (p + 2 - 1) (by omega)
  have hcu : (UInt256.lt (MachineState.readWord mem 8224 +
      (rowL1 mem pa pb (p + 2) i).carry)
      (rowL1 mem pa pb (p + 2) i).carry).toNat ≤ 1 := by
    rw [word_toNat_lt']
    split <;> omega
  have hcv : (UInt256.lt (MachineState.readWord (rowMid mem pa pb (p + 2) i) 8224 +
      (rowL2 mem pa pb (p + 2) i).carry)
      (rowL2 mem pa pb (p + 2) i).carry).toNat ≤ 1 := by
    rw [word_toNat_lt']
    split <;> omega
  have hFtn : (MachineState.readWord (rowMem mem pa pb (p + 2) i) 8224).toNat =
      (UInt256.lt (MachineState.readWord mem 8224 + (rowL1 mem pa pb (p + 2) i).carry)
        (rowL1 mem pa pb (p + 2) i).carry).toNat +
      (UInt256.lt (MachineState.readWord (rowMid mem pa pb (p + 2) i) 8224 +
        (rowL2 mem pa pb (p + 2) i).carry)
        (rowL2 mem pa pb (p + 2) i).carry).toNat := by
    rw [readWord_rowMem_tn, hL2tnp, hMDtnp, hL2tn,
      Challenge.EvmProof.Word.word_toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hFts : (MachineState.readWord (rowMem mem pa pb (p + 2) i) 8256).toNat =
      (MachineState.readWord (rowMid mem pa pb (p + 2) i) 8224 +
        (rowL2 mem pa pb (p + 2) i).carry).toNat := by
    rw [readWord_rowMem_top, hL2tn]
  have hA : (UInt256.lt (MachineState.readWord mem 8224 +
        (rowL1 mem pa pb (p + 2) i).carry)
        (rowL1 mem pa pb (p + 2) i).carry).toNat * Limbs.radix +
      (MachineState.readWord (rowMid mem pa pb (p + 2) i) 8224).toNat =
      (MachineState.readWord mem 8224).toNat +
        (rowL1 mem pa pb (p + 2) i).carry.toNat := by
    rw [hMDtn, radix_eq]
    exact add_carry_split (MachineState.readWord mem 8224)
      (rowL1 mem pa pb (p + 2) i).carry
  have hB : (UInt256.lt (MachineState.readWord (rowMid mem pa pb (p + 2) i) 8224 +
        (rowL2 mem pa pb (p + 2) i).carry)
        (rowL2 mem pa pb (p + 2) i).carry).toNat * Limbs.radix +
      (MachineState.readWord (rowMid mem pa pb (p + 2) i) 8224 +
        (rowL2 mem pa pb (p + 2) i).carry).toNat =
      (MachineState.readWord (rowMid mem pa pb (p + 2) i) 8224).toNat +
        (rowL2 mem pa pb (p + 2) i).carry.toNat := by
    rw [radix_eq]
    exact add_carry_split (MachineState.readWord (rowMid mem pa pb (p + 2) i) 8224)
      (rowL2 mem pa pb (p + 2) i).carry
  have hC : (rowC0 (rowL1 mem pa pb (p + 2) i).memory (p + 2)).toNat * Limbs.radix =
      (l1Val mem (rowBi mem pb (p + 2) i) pa (p + 2) 0).toNat +
        (MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
          (rowMu (rowL1 mem pa pb (p + 2) i).memory (p + 2)).toNat := by
    rw [radix_eq, ← hT0, ← hM0]
    exact c0_spec
      (MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory (32 * (p + 2) - 32))
      (MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory 9376)
      (MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory (8224 + 32 * (p + 2)))
      (by rw [hM0, hMinvR]; exact hminv)
  have hD0 := l2_invariant (rowMid mem pa pb (p + 2) i)
    (rowMu (rowL1 mem pa pb (p + 2) i).memory (p + 2))
    (rowC0 (rowL1 mem pa pb (p + 2) i).memory (p + 2)) (p + 2) hn32 (p + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hD0
  have hD : limbSum (fun k => (l2Val (rowMid mem pa pb (p + 2) i)
          (rowMu (rowL1 mem pa pb (p + 2) i).memory (p + 2))
          (rowC0 (rowL1 mem pa pb (p + 2) i).memory (p + 2)) (p + 2) k).toNat)
          (p + 1) +
        (rowL2 mem pa pb (p + 2) i).carry.toNat * Limbs.radix ^ (p + 1) =
      (rowC0 (rowL1 mem pa pb (p + 2) i).memory (p + 2)).toNat +
        (limbSum (fun k => (MachineState.readWord (rowMid mem pa pb (p + 2) i)
            (8256 + 32 * (p - k))).toNat) (p + 1) +
          (rowMu (rowL1 mem pa pb (p + 2) i).memory (p + 2)).toNat *
            limbSum (fun k => (MachineState.readWord (rowMid mem pa pb (p + 2) i)
              (32 * (p - k))).toNat) (p + 1)) := hD0
  have hstF : ∀ k, k < p + 1 →
      (MachineState.readWord (rowMid mem pa pb (p + 2) i)
        (8256 + 32 * (p - k))).toNat =
      (l1Val mem (rowBi mem pb (p + 2) i) pa (p + 2) (k + 1)).toNat := by
    intro k hk
    have h1 : MachineState.readWord (rowMid mem pa pb (p + 2) i)
        (8256 + 32 * (p - k)) =
        MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory
          (8256 + 32 * (p - k)) := by
      rw [rowMid_def]
      exact readWord_midMem_high _ _ _ (by omega)
    have h2 : MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory
        (8256 + 32 * (p - k)) =
        l1Val mem (rowBi mem pb (p + 2) i) pa (p + 2) (k + 1) := by
      have h3 := readWord_l1Step_val mem (rowBi mem pb (p + 2) i) pa (p + 2) (k + 1)
        hn32 (by omega) hpaFit (p + 2) (by omega) (Nat.le_refl _)
      simp only [tAddr] at h3
      have haddr : 8256 + 32 * (p + 2 - 1 - (k + 1)) = 8256 + 32 * (p - k) := by omega
      rw [haddr] at h3
      exact h3
    rw [h1, h2]
  have hE : limbSum (fun k => (MachineState.readWord (rowMid mem pa pb (p + 2) i)
          (8256 + 32 * (p - k))).toNat) (p + 1) * Limbs.radix +
        (l1Val mem (rowBi mem pb (p + 2) i) pa (p + 2) 0).toNat =
      limbSum (fun k => (l1Val mem (rowBi mem pb (p + 2) i) pa (p + 2) k).toNat)
        (p + 2) := by
    rw [limbSum_congr (p + 1) hstF]
    exact limbSum_shift
      (fun k => (l1Val mem (rowBi mem pb (p + 2) i) pa (p + 2) k).toNat) (p + 1)
  have hmm := limbSum_fastRepresents hm
  simp only [Nat.zero_add] at hmm
  have hsmF : ∀ k, k < p + 1 →
      (MachineState.readWord (rowMid mem pa pb (p + 2) i) (32 * (p - k))).toNat =
      (MachineState.readWord mem (32 * (p + 2 - 1 - (k + 1)))).toNat := by
    intro k hk
    have h1 : MachineState.readWord (rowMid mem pa pb (p + 2) i) (32 * (p - k)) =
        MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory (32 * (p - k)) := by
      rw [rowMid_def]
      exact readWord_midMem_low' _ _ _ (by omega)
    have h2 : MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory
        (32 * (p - k)) = MachineState.readWord mem (32 * (p - k)) :=
      readWord_l1Step_low mem (rowBi mem pb (p + 2) i) pa (p + 2) (32 * (p - k))
        (p + 2) (by omega)
    have haddr : 32 * (p + 2 - 1 - (k + 1)) = 32 * (p - k) := by omega
    rw [h1, h2, haddr]
  have hF : limbSum (fun k => (MachineState.readWord (rowMid mem pa pb (p + 2) i)
          (32 * (p - k))).toNat) (p + 1) * Limbs.radix +
        (MachineState.readWord mem (32 * (p + 2) - 32)).toNat = mm := by
    rw [limbSum_congr (p + 1) hsmF]
    have h0 : 32 * (p + 2) - 32 = 32 * (p + 2 - 1 - 0) := by omega
    rw [h0]
    rw [limbSum_shift (fun k =>
      (MachineState.readWord mem (32 * (p + 2 - 1 - k))).toNat) (p + 1)]
    exact hmm
  have hG : limbSum (fun k => (l1Val mem (rowBi mem pb (p + 2) i) pa (p + 2) k).toNat)
        (p + 2) +
      (rowL1 mem pa pb (p + 2) i).carry.toNat *
        (Limbs.radix ^ (p + 1) * Limbs.radix) =
      tlow + (rowBi mem pb (p + 2) i).toNat * a := by
    rw [← hpow]
    exact l1_row mem (rowBi mem pb (p + 2) i) pa (p + 2) tlow a hn32 hpaFit ha ht
  rw [lowValue_rowMem mem pa pb p i hn32, hFtn, hFts, hpow]
  exact row_alg hA hB hC hD hE hF hG

/-! ## The prologue zeroes the CIOS accumulator

`CALLDATACOPY(T_, CALLDATASIZE, s32 + 64)` copies `64 + 32 * n` bytes from the
end of the calldata, which the EVM zero-pads, so `t[n+1]`, `t[n]` and the whole
`t` block start at zero. -/

theorem natToBytesPadded_zero_byte (width k : Nat) (h : k < width) :
    (Data.Bytes.natToBytesPadded 0 width)[k]?.getD 0 = 0 := by
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD 0 width k h]
  simp

theorem readWord_calldata_zero (mem cd : ByteArray) (len dst a : Nat)
    (hlo : dst ≤ a) (hhi : a + 32 ≤ dst + len) :
    MachineState.readWord
        (MachineState.writeBytes mem (MachineState.readPadded cd cd.size len) dst) a =
      UInt256.ofNat 0 := by
  have hzero : MachineState.readWord
      (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 0 32) a) a =
      UInt256.ofNat 0 :=
    Challenge.EvmProof.Memory.readWord_writeBytes_of_lt mem a 0 (by norm_num)
  have hpad : MachineState.readPadded
      (MachineState.writeBytes mem (MachineState.readPadded cd cd.size len) dst) a 32 =
      MachineState.readPadded
        (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 0 32) a) a 32 := by
    apply Challenge.EvmProof.Memory.readPadded_congr
    intro i hi
    rw [MachineState.writeBytes_getElem?_getD, MachineState.writeBytes_getElem?_getD,
      Challenge.EvmProof.Memory.readPadded_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
      if_pos (by omega), if_pos (by omega),
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos (by omega),
      Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le _ _ (by omega),
      natToBytesPadded_zero_byte 32 (a + i - a) (by omega)]
  rw [← hzero]
  unfold MachineState.readWord
  rw [hpad]

theorem readWord_mpZeroed_zero (s : State) (mem : ByteArray) (n a : Nat)
    (hlo : 8192 ≤ a) (hhi : a + 32 ≤ 8256 + 32 * n) :
    MachineState.readWord (mpZeroed s mem n) a = UInt256.ofNat 0 := by
  simp only [mpZeroed]
  exact readWord_calldata_zero mem s.executionEnv.calldata (64 + 32 * n) 8192 a hlo
    (by omega)

theorem fastRepresents_mpZeroed (s : State) (mem : ByteArray) (n : Nat) :
    Model.FastRepresents (mpZeroed s mem n) 8256 n 0 := by
  rw [Model.fastRepresents_zero_iff]
  intro j hj
  rw [readWord_mpZeroed_zero s mem n (8256 + 32 * j) (by omega) (by omega)]
  simp

theorem readWord_mpZeroed_tn (s : State) (mem : ByteArray) (n : Nat) :
    MachineState.readWord (mpZeroed s mem n) 8224 = UInt256.ofNat 0 :=
  readWord_mpZeroed_zero s mem n 8224 (by omega) (by omega)

/-! ## The outer loop -/

/-- The `(n+1)`-limb CIOS accumulator `t = t[n]·rad^n + t_low`. -/
def tValue (mem : ByteArray) (n : Nat) : Nat :=
  (MachineState.readWord mem 8224).toNat * Limbs.radix ^ n +
    Csub.lowValue mem 8256 n n

private theorem div_of_mul {x y r : Nat} (hr : 0 < r) (h : x * r = y) : y / r = x := by
  have hy : y / r = x * r / r := by rw [h]
  rw [hy, Nat.mul_div_assoc x (dvd_refl r), Nat.div_self hr, Nat.mul_one]

/-- Consuming one more radix digit of `v`. -/
theorem mod_pow_succ (v i : Nat) :
    v % Limbs.radix ^ (i + 1) =
      v % Limbs.radix ^ i + v / Limbs.radix ^ i % Limbs.radix * Limbs.radix ^ i := by
  have h1 := limbSum_digits v (i + 1)
  have h2 := limbSum_digits v i
  rw [limbSum_succ] at h1
  rw [h2] at h1
  exact h1.symm

/-- The outer CIOS invariant: after `i` rows, `t_i · rad^i = a · B_i + Q_i · m`
with `B_i` the value of the `i` consumed limbs of `b`, and `t_i < 2 m`. -/
theorem rows_invariant (s : State) (mem : ByteArray) (pa pb p : Nat) (a b mm : Nat)
    (hn32 : p + 2 ≤ 32)
    (hpaFit : pa + 32 * (p + 2) ≤ 8192) (hpbFit : pb + 32 * (p + 2) ≤ 8192)
    (ha : Model.FastRepresents mem pa (p + 2) a)
    (hb : Model.FastRepresents mem pb (p + 2) b)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (ham : a < mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    ∀ i, i ≤ p + 2 → ∃ Q,
      tValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) (p + 2) *
          Limbs.radix ^ i = a * (b % Limbs.radix ^ i) + Q * mm ∧
        tValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) (p + 2) < 2 * mm := by
  intro i
  induction i with
  | zero =>
      intro _
      have hlow0 : Csub.lowValue (mpZeroed s mem (p + 2)) 8256 (p + 2) (p + 2) = 0 :=
        Model.fastRepresents_value_unique
          (Csub.fastRepresents_lowValue (mpZeroed s mem (p + 2)) 8256 (p + 2))
          (fastRepresents_mpZeroed s mem (p + 2))
      have hzero : tValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) 0)
          (p + 2) = 0 := by
        show tValue (mpZeroed s mem (p + 2)) (p + 2) = 0
        simp only [tValue, hlow0, readWord_mpZeroed_tn,
          Challenge.EvmProof.Word.word_toNat_ofNat]
        simp
      exact ⟨0, by rw [hzero, pow_zero, Nat.mod_one]; simp, by rw [hzero]; omega⟩
  | succ i ih =>
      intro hi
      obtain ⟨Q, hinv, hlt⟩ := ih (by omega)
      simp only [tValue] at hinv hlt ⊢
      simp only [rowsMem]
      have hpaR : Model.FastRepresents
          (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) pa (p + 2) a :=
        fastRepresents_monpro_preserved s mem pa pb (p + 2) i pa (p + 2) a hn32
          hpaFit ha
      have hpbR : Model.FastRepresents
          (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) pb (p + 2) b :=
        fastRepresents_monpro_preserved s mem pa pb (p + 2) i pb (p + 2) b hn32
          hpbFit hb
      have hmR : Model.FastRepresents
          (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) 0 (p + 2) mm :=
        fastRepresents_monpro_preserved s mem pa pb (p + 2) i 0 (p + 2) mm hn32
          (by omega) hm
      have hminvR : ((MachineState.readWord
            (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
            (32 * (p + 2) - 32)).toNat *
          (MachineState.readWord
            (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) 9376).toNat + 1) %
          2 ^ 256 = 0 := by
        rw [readWord_monpro_preserved s mem pa pb (p + 2) i (32 * (p + 2) - 32) hn32
            (Or.inl (by omega)),
          readWord_monpro_preserved s mem pa pb (p + 2) i 9376 hn32 (Or.inr (by omega))]
        exact hminv
      have hrow := row_equation (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
        pa pb p i a mm
        (Csub.lowValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) 8256
          (p + 2) (p + 2))
        hn32 hpaFit hpaR hmR
        (Csub.fastRepresents_lowValue
          (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) 8256 (p + 2)) hminvR
      have hbi : (rowBi (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
          pb (p + 2) i).toNat = b / Limbs.radix ^ i % Limbs.radix := by
        simp only [rowBi]
        exact Model.readLimb_of_fastRepresents hpbR (by omega)
      have hdiv : Limbs.radix ∣
          (MachineState.readWord (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
              8224).toNat * Limbs.radix ^ (p + 2) +
            Csub.lowValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) 8256
              (p + 2) (p + 2) +
            a * (rowBi (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
              pb (p + 2) i).toNat +
            (rowMu (rowL1 (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
              pa pb (p + 2) i).memory (p + 2)).toNat * mm := by
        refine ⟨(MachineState.readWord (rowMem
              (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) pa pb (p + 2) i)
              8224).toNat * Limbs.radix ^ (p + 2) +
            Csub.lowValue (rowMem (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
              pa pb (p + 2) i) 8256 (p + 2) (p + 2), ?_⟩
        rw [← hrow]
        ring
      have hquot := div_of_mul Limbs.radix_pos hrow
      obtain ⟨hstep1, hstep2⟩ := Model.cios_step (β := Limbs.radix) (m := mm) (a := a)
        (bpre := b % Limbs.radix ^ i)
        (bi := (rowBi (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
          pb (p + 2) i).toNat)
        (t := (MachineState.readWord
            (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) 8224).toNat *
            Limbs.radix ^ (p + 2) +
          Csub.lowValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) 8256
            (p + 2) (p + 2))
        (Q := Q)
        (mu := (rowMu (rowL1 (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
          pa pb (p + 2) i).memory (p + 2)).toNat) (i := i)
        Limbs.radix_pos ham (word_lt_size _) hlt (word_lt_size _) hinv hdiv
      refine ⟨Q + (rowMu (rowL1 (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
        pa pb (p + 2) i).memory (p + 2)).toNat * Limbs.radix ^ i, ?_, ?_⟩
      · rw [← hquot, hstep1, mod_pow_succ, hbi]
      · rw [← hquot]
        exact hstep2

/-! ## The two `MONPRO` postconditions -/

/-- The CIOS accumulator's top limb never exceeds one: this is the `t < 2 m`
bound of the row invariant together with `m < rad ^ n`. -/
theorem monpro_tn_le_one (s : State) (mem : ByteArray) (pa pb p : Nat) (a b mm : Nat)
    (hn32 : p + 2 ≤ 32)
    (hpaFit : pa + 32 * (p + 2) ≤ 8192) (hpbFit : pb + 32 * (p + 2) ≤ 8192)
    (ha : Model.FastRepresents mem pa (p + 2) a)
    (hb : Model.FastRepresents mem pb (p + 2) b)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (ham : a < mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    (MachineState.readWord (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2))
      8224).toNat ≤ 1 := by
  obtain ⟨-, -, hlt⟩ := rows_invariant s mem pa pb p a b mm hn32 hpaFit hpbFit ha hb hm
    ham hmpos hminv (p + 2) (Nat.le_refl _)
  simp only [tValue] at hlt
  have hmlt : mm < Limbs.radix ^ (p + 2) := hm.1
  have hlow : Csub.lowValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2))
      8256 (p + 2) (p + 2) < Limbs.radix ^ (p + 2) := Csub.lowValue_lt _ _ _ _
  by_contra hcon
  have hge : 2 ≤ (MachineState.readWord
      (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) 8224).toNat := by omega
  have hmul : 2 * Limbs.radix ^ (p + 2) ≤
      (MachineState.readWord (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2))
        8224).toNat * Limbs.radix ^ (p + 2) := Nat.mul_le_mul_right _ hge
  omega

/-- `MONPRO` followed by `CSUB` writes the Montgomery product
`a · b · (rad ^ n)⁻¹ mod m` into the destination block. -/
theorem monpro_represents (s : State) (mem : ByteArray) (pa pb p pdst : Nat)
    (a b mm : Nat) (hn32 : p + 2 ≤ 32)
    (hpaFit : pa + 32 * (p + 2) ≤ 8192) (hpbFit : pb + 32 * (p + 2) ≤ 8192)
    (ha : Model.FastRepresents mem pa (p + 2) a)
    (hb : Model.FastRepresents mem pb (p + 2) b)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (hodd : mm % 2 = 1) (ham : a < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    Model.FastRepresents
      (Csub.csResultMemory
        (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) (p + 2) pdst)
      pdst (p + 2) (Model.montMul mm (Limbs.radix ^ (p + 2)) a b) := by
  have hmpos : 0 < mm := by omega
  obtain ⟨Q, hinv, hlt⟩ := rows_invariant s mem pa pb p a b mm hn32 hpaFit hpbFit ha hb
    hm ham hmpos hminv (p + 2) (Nat.le_refl _)
  have htn1 := monpro_tn_le_one s mem pa pb p a b mm hn32 hpaFit hpbFit ha hb hm ham
    hmpos hminv
  have hbmod : b % Limbs.radix ^ (p + 2) = b := Nat.mod_eq_of_lt hb.1
  rw [hbmod] at hinv
  have hcop : Nat.Coprime (Limbs.radix ^ (p + 2)) mm :=
    Model.coprime_radix_pow_of_odd hodd (p + 2)
  have hval : Model.montMul mm (Limbs.radix ^ (p + 2)) a b =
      tValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) (p + 2) % mm :=
    Model.montMul_eq_mod_of_mul_eq hmpos hcop hinv
  have hmR : Model.FastRepresents
      (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) 0 (p + 2) mm :=
    fastRepresents_monpro_preserved s mem pa pb (p + 2) (p + 2) 0 (p + 2) mm hn32
      (by omega) hm
  rw [hval]
  simp only [tValue] at hlt ⊢
  exact Csub.csub_correct (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2))
    (p + 2)
    (Csub.lowValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) 8256
      (p + 2) (p + 2))
    mm
    (MachineState.readWord (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2))
      8224).toNat
    pdst (by omega) hn32
    (Csub.fastRepresents_lowValue
      (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) 8256 (p + 2))
    hmR rfl htn1 hmpos hlt

/-- The whole call with the `t[n] ≤ 1` side condition discharged. -/
def gasSteps_monproFull (s : State) (mem : ByteArray) (pa pb p : Nat) (a b mm : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : p + 2 ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * (p + 2) ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * (p + 2) ≤ 8192)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * (p + 2)))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * (p + 2)))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * (p + 2) - 32))
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hdstFit : pdst.toNat + 32 * (p + 2) ≤ 9472)
    (ha : Model.FastRepresents mem pa (p + 2) a)
    (hb : Model.FastRepresents mem pb (p + 2) b)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (ham : a < mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    Challenge.EvmProof.GasSteps
      (mpEntryState s mem pa pb pdst ret rest)
      (Csub.csReturnedState s
        (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) (p + 2) (p + 2)
        pdst ret rest) :=
  gasSteps_monproCsub s mem pa pb (p + 2) pdst ret rest hcap hrun hcode hfork hnp hact
    (by omega) hn32 hpa (by omega) hpb (by omega) hcds hs32 htl hml hjump hdstFit
    (monpro_tn_le_one s mem pa pb p a b mm hn32 hpaFit hpbFit ha hb hm ham hmpos hminv)

/-! ## Frame lemmas

The configuration words `V_S32 = 9344`, `V_MINV = 9376`, `V_ML = 9408`,
`V_TL = 9440` and `V_EOFF = 9472` are written once by `Fast.Setup` and read by
every subroutine.  No transformer a `MONPRO` call applies writes at or above
`9280 = 8256 + 32 * 32`, so all five survive a whole run; the lemmas below say
that once per transformer, at the `readWord` level, so a driver can carry the
frame across calls instead of threading it. -/

/-- One 32-byte store leaves every other word alone.  This is the shape
`Fast.Exp.storeWord` unfolds to. -/
theorem readWord_storeWord_outside (mem : ByteArray) (w dst addr : Nat)
    (hout : addr + 32 ≤ dst ∨ dst + 32 ≤ addr) :
    MachineState.readWord
        (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded w 32) dst) addr =
      MachineState.readWord mem addr := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  exact hout

/-- One `MCOPY` leaves every word outside the destination alone.  This is the
shape `Fast.Exp.mcopyMem` unfolds to. -/
theorem readWord_mcopy_outside (mem : ByteArray) (src dst sz addr : Nat)
    (hout : addr + 32 ≤ dst ∨ dst + sz ≤ addr) :
    MachineState.readWord
        (MachineState.writeBytes mem (MachineState.readPadded mem src sz) dst) addr =
      MachineState.readWord mem addr := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [Challenge.EvmProof.Memory.readPadded_size]
  exact hout

/-- The `CALLDATACOPY` prologue writes exactly `[8192, 8256 + 32 * n)`. -/
theorem mpZeroed_readWord_outside (s : State) (mem : ByteArray) (n addr : Nat)
    (hout : addr + 32 ≤ 8192 ∨ 8256 + 32 * n ≤ addr) :
    MachineState.readWord (mpZeroed s mem n) addr = MachineState.readWord mem addr := by
  simp only [mpZeroed]
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [Challenge.EvmProof.Memory.readPadded_size]
  omega

/-- The `n` CIOS rows write only inside `[8192, 9280)`. -/
theorem rowsMem_readWord_outside (mem : ByteArray) (pa pb n i addr : Nat)
    (hn : n ≤ 32) (hout : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (rowsMem mem pa pb n i) addr =
      MachineState.readWord mem addr :=
  readWord_rowsMem mem pa pb n addr hn hout i

/-- `CSUB` writes only inside `SUBB = [7168, 7168 + 32 * n)` and the
destination block. -/
theorem csResultMemory_readWord_outside (memory : ByteArray) (n pdst addr : Nat)
    (hn : 1 ≤ n)
    (hsubb : addr + 32 ≤ 7168 ∨ 7168 + 32 * n ≤ addr)
    (hdst : addr + 32 ≤ pdst ∨ pdst + 32 * n ≤ addr) :
    MachineState.readWord (Csub.csResultMemory memory n pdst) addr =
      MachineState.readWord memory addr := by
  simp only [Csub.csResultMemory]
  rw [readWord_mcopy_outside (Csub.csStep memory n n).memory
    (Csub.csSrc memory n n).toNat pdst (32 * n) addr hdst]
  exact Csub.csStep_readWord_disjoint memory n addr hn hsubb n (Nat.le_refl n)

/-- The memory a whole `MonPro(pa, pb) → pd` call leaves behind. -/
def monproMem (s : State) (mem : ByteArray) (pa pb n pdst : Nat) : ByteArray :=
  Csub.csResultMemory (rowsMem (mpZeroed s mem n) pa pb n n) n pdst

theorem monproMem_def (s : State) (mem : ByteArray) (pa pb n pdst : Nat) :
    monproMem s mem pa pb n pdst =
      Csub.csResultMemory (rowsMem (mpZeroed s mem n) pa pb n n) n pdst := rfl

/-- `gasSteps_monproFull` ends with exactly this memory. -/
theorem csReturnedState_memory_monproMem (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256) :
    (Csub.csReturnedState s (rowsMem (mpZeroed s mem n) pa pb n n) n n pdst ret
      rest).memory = monproMem s mem pa pb n pdst.toNat := rfl

/-- Every word outside `SUBB`, outside the CIOS scratch `[8192, 9280)` and
outside the destination survives a `MONPRO` call. -/
theorem monproMem_readWord_outside (s : State) (mem : ByteArray)
    (pa pb n pdst addr : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hsubb : addr + 32 ≤ 7168 ∨ 7168 + 32 * n ≤ addr)
    (hscratch : addr + 32 ≤ 8192 ∨ 9280 ≤ addr)
    (hdst : addr + 32 ≤ pdst ∨ pdst + 32 * n ≤ addr) :
    MachineState.readWord (monproMem s mem pa pb n pdst) addr =
      MachineState.readWord mem addr := by
  rw [monproMem_def,
    csResultMemory_readWord_outside _ n pdst addr hn hsubb hdst,
    rowsMem_readWord_outside _ pa pb n n addr hn32 hscratch,
    mpZeroed_readWord_outside s mem n addr (by omega)]

/-- Everything at or above `9280` survives, given only that the destination is
one of the named blocks below `T_ = 8192`. -/
theorem monproMem_readWord_high (s : State) (mem : ByteArray)
    (pa pb n pdst addr : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hdst : pdst + 32 * n ≤ 8192) (haddr : 9280 ≤ addr) :
    MachineState.readWord (monproMem s mem pa pb n pdst) addr =
      MachineState.readWord mem addr :=
  monproMem_readWord_outside s mem pa pb n pdst addr hn hn32 (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr (by omega))

/-- The five configuration words `V_S32`, `V_MINV`, `V_ML`, `V_TL`, `V_EOFF`
are unchanged by a `MONPRO` call. -/
theorem monproMem_frame (s : State) (mem : ByteArray) (pa pb n pdst : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (hdst : pdst + 32 * n ≤ 8192) :
    MachineState.readWord (monproMem s mem pa pb n pdst) 9344 =
        MachineState.readWord mem 9344 ∧
      MachineState.readWord (monproMem s mem pa pb n pdst) 9376 =
        MachineState.readWord mem 9376 ∧
      MachineState.readWord (monproMem s mem pa pb n pdst) 9408 =
        MachineState.readWord mem 9408 ∧
      MachineState.readWord (monproMem s mem pa pb n pdst) 9440 =
        MachineState.readWord mem 9440 ∧
      MachineState.readWord (monproMem s mem pa pb n pdst) 9472 =
        MachineState.readWord mem 9472 :=
  ⟨monproMem_readWord_high s mem pa pb n pdst 9344 hn hn32 hdst (by omega),
   monproMem_readWord_high s mem pa pb n pdst 9376 hn hn32 hdst (by omega),
   monproMem_readWord_high s mem pa pb n pdst 9408 hn hn32 hdst (by omega),
   monproMem_readWord_high s mem pa pb n pdst 9440 hn hn32 hdst (by omega),
   monproMem_readWord_high s mem pa pb n pdst 9472 hn hn32 hdst (by omega)⟩

/-- Every represented block disjoint from `SUBB`, from the CIOS scratch and
from the destination survives a `MONPRO` call. -/
theorem monproMem_fastRepresents_outside (s : State) (mem : ByteArray)
    (pa pb n pdst ptr cnt v : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hsubb : ptr + 32 * cnt ≤ 7168 ∨ 7168 + 32 * n ≤ ptr)
    (hscratch : ptr + 32 * cnt ≤ 8192 ∨ 9280 ≤ ptr)
    (hdst : ptr + 32 * cnt ≤ pdst ∨ pdst + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (monproMem s mem pa pb n pdst) ptr cnt v := by
  refine (Model.fastRepresents_congr
    (a := mem) (b := monproMem s mem pa pb n pdst) ?_ v).1 hrep
  intro j hj
  exact (monproMem_readWord_outside s mem pa pb n pdst (ptr + 32 * j) hn hn32
    (by omega) (by omega) (by omega)).symm

/-- The destination block of a `MONPRO` call, in `monproMem` form. -/
theorem monproMem_represents (s : State) (mem : ByteArray) (pa pb p pdst : Nat)
    (a b mm : Nat) (hn32 : p + 2 ≤ 32)
    (hpaFit : pa + 32 * (p + 2) ≤ 8192) (hpbFit : pb + 32 * (p + 2) ≤ 8192)
    (ha : Model.FastRepresents mem pa (p + 2) a)
    (hb : Model.FastRepresents mem pb (p + 2) b)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (hodd : mm % 2 = 1) (ham : a < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    Model.FastRepresents (monproMem s mem pa pb (p + 2) pdst) pdst (p + 2)
      (Model.montMul mm (Limbs.radix ^ (p + 2)) a b) :=
  monpro_represents s mem pa pb p pdst a b mm hn32 hpaFit hpbFit ha hb hm hodd ham
    hminv

end Challenge.Modexp.Submission.Proofs.Fast.Monpro
