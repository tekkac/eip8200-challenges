import Challenge.Modexp.Submission.Proofs.Limbs
import Challenge.Modexp.Submission.Proofs.Algorithm
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option warningAsError true
/-!
# Arithmetic model of the Montgomery fast path

This module contains no EVM reasoning.  It provides

* `FastRepresents`, the big-endian-limb view of an `n`-limb block (most
  significant limb at the base address), with the same interface as
  `Limbs.Represents`;
* Montgomery multiplication over `Nat` (`montMul`) and the CIOS row lemma;
* modular doubling chains, Horner base reduction, left-to-right
  square-and-multiply, and the Newton iteration for `-m⁻¹ mod 2^256`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Model

open EvmSemantics
open Challenge.Modexp.Submission.Proofs

/-! ## Big-endian limb blocks -/

/-- The limbs of the block at `ptr`, least significant first.  Limb `k`
(counted from the least significant) is stored at `ptr + 32 * (count - 1 - k)`. -/
def fastLimbs (memory : ByteArray) (ptr count : Nat) : List Nat :=
  (List.range count).map fun k =>
    (MachineState.readWord memory (ptr + 32 * (count - 1 - k))).toNat

/-- `memory[ptr .. ptr + 32*count]` is the big-endian-limb encoding of
`value`: the most significant limb sits at `ptr`. -/
def FastRepresents (memory : ByteArray) (ptr count value : Nat) : Prop :=
  value < Limbs.radix ^ count ∧
    fastLimbs memory ptr count = Limbs.limbDigits count value

@[simp] theorem length_fastLimbs (memory : ByteArray) (ptr count : Nat) :
    (fastLimbs memory ptr count).length = count := by
  simp [fastLimbs]

theorem fastLimb_lt (memory : ByteArray) (ptr count : Nat)
    {digit : Nat} (hdigit : digit ∈ fastLimbs memory ptr count) :
    digit < Limbs.radix := by
  simp only [fastLimbs, List.mem_map] at hdigit
  rcases hdigit with ⟨k, _, rfl⟩
  exact (MachineState.readWord memory (ptr + 32 * (count - 1 - k))).val.isLt

theorem fastLimbs_getElem (memory : ByteArray) (ptr count k : Nat)
    (hk : k < (fastLimbs memory ptr count).length) :
    (fastLimbs memory ptr count)[k] =
      (MachineState.readWord memory (ptr + 32 * (count - 1 - k))).toNat := by
  simp [fastLimbs]

/-- The bridge to the project's little-endian-index convention: the fast
limb list is the reversal of `Limbs.memoryLimbs`. -/
theorem fastLimbs_eq_reverse_memoryLimbs (memory : ByteArray) (ptr count : Nat) :
    fastLimbs memory ptr count = (Limbs.memoryLimbs memory ptr count).reverse := by
  apply List.ext_getElem
  · simp
  · intro k hk _
    have hk' : k < count := by simpa using hk
    rw [List.getElem_reverse]
    simp [fastLimbs, Limbs.memoryLimbs]

theorem memoryLimbs_eq_reverse_fastLimbs (memory : ByteArray) (ptr count : Nat) :
    Limbs.memoryLimbs memory ptr count = (fastLimbs memory ptr count).reverse := by
  rw [fastLimbs_eq_reverse_memoryLimbs, List.reverse_reverse]

theorem value_of_fastRepresents {memory : ByteArray} {ptr count value : Nat}
    (hrep : FastRepresents memory ptr count value) :
    Nat.ofDigits Limbs.radix (fastLimbs memory ptr count) = value := by
  rw [hrep.2, Limbs.value_limbDigits]

theorem fastRepresents_lt {memory : ByteArray} {ptr count value : Nat}
    (hrep : FastRepresents memory ptr count value) :
    value < Limbs.radix ^ count :=
  hrep.1

theorem fastRepresents_value_unique {memory : ByteArray} {ptr count a b : Nat}
    (ha : FastRepresents memory ptr count a)
    (hb : FastRepresents memory ptr count b) : a = b := by
  rw [← value_of_fastRepresents ha, ← value_of_fastRepresents hb]

theorem fastRepresents_iff_value {memory : ByteArray} {ptr count value : Nat}
    (hvalue : value < Limbs.radix ^ count) :
    FastRepresents memory ptr count value ↔
      Nat.ofDigits Limbs.radix (fastLimbs memory ptr count) = value := by
  constructor
  · exact value_of_fastRepresents
  · intro heq
    refine ⟨hvalue, ?_⟩
    apply Nat.ofDigits_inj_of_len_eq Limbs.radix_gt_one
    · rw [length_fastLimbs, Limbs.length_limbDigits hvalue]
    · exact fun digit hdigit => fastLimb_lt _ _ _ hdigit
    · exact fun digit hdigit => Limbs.limbDigits_lt hdigit
    · rw [heq, Limbs.value_limbDigits]

private theorem getElem_eq_div_mod_ofDigits (digits : List Nat) (index : Nat)
    (hindex : index < digits.length) (hdigits : ∀ d ∈ digits, d < Limbs.radix) :
    digits[index] =
      Nat.ofDigits Limbs.radix digits / Limbs.radix ^ index % Limbs.radix := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop index Limbs.radix_pos digits hdigits,
    List.drop_eq_getElem_cons hindex]
  simp only [Nat.ofDigits_cons]
  rw [Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (hdigits digits[index] (List.getElem_mem hindex))]

/-- Limb `k` (from the least significant) of a represented block. -/
theorem readLimb_of_fastRepresents {memory : ByteArray} {ptr count value k : Nat}
    (hrep : FastRepresents memory ptr count value) (hk : k < count) :
    (MachineState.readWord memory (ptr + 32 * (count - 1 - k))).toNat =
      value / Limbs.radix ^ k % Limbs.radix := by
  have hlen : k < (fastLimbs memory ptr count).length := by simpa using hk
  have hget := getElem_eq_div_mod_ofDigits (fastLimbs memory ptr count) k hlen
    (fun d hd => fastLimb_lt memory ptr count hd)
  rw [value_of_fastRepresents hrep, fastLimbs_getElem] at hget
  exact hget

/-- The word at offset `32 * j` from the base holds limb `count - 1 - j`. -/
theorem readWord_of_fastRepresents {memory : ByteArray} {ptr count value j : Nat}
    (hrep : FastRepresents memory ptr count value) (hj : j < count) :
    (MachineState.readWord memory (ptr + 32 * j)).toNat =
      value / Limbs.radix ^ (count - 1 - j) % Limbs.radix := by
  have h := readLimb_of_fastRepresents hrep (k := count - 1 - j) (by omega)
  rwa [show count - 1 - (count - 1 - j) = j by omega] at h

/-- Introduction rule: a block whose limbs are the radix digits of `value`
represents `value`. -/
theorem fastRepresents_of_limbs {memory : ByteArray} {ptr count value : Nat}
    (hvalue : value < Limbs.radix ^ count)
    (hlimbs : ∀ k, k < count →
      (MachineState.readWord memory (ptr + 32 * (count - 1 - k))).toNat =
        value / Limbs.radix ^ k % Limbs.radix) :
    FastRepresents memory ptr count value := by
  refine ⟨hvalue, ?_⟩
  apply List.ext_getElem
  · rw [length_fastLimbs, Limbs.length_limbDigits hvalue]
  · intro k hk hk'
    have hkc : k < count := by simpa using hk
    rw [fastLimbs_getElem, hlimbs k hkc,
      getElem_eq_div_mod_ofDigits _ k hk' (fun d hd => Limbs.limbDigits_lt hd),
      Limbs.value_limbDigits]

theorem fastRepresents_zero_iff (memory : ByteArray) (ptr count : Nat) :
    FastRepresents memory ptr count 0 ↔
      ∀ j, j < count → (MachineState.readWord memory (ptr + 32 * j)).toNat = 0 := by
  constructor
  · intro hrep j hj
    rw [readWord_of_fastRepresents hrep hj, Nat.zero_div, Nat.zero_mod]
  · intro hzero
    apply fastRepresents_of_limbs (pow_pos Limbs.radix_pos count)
    intro k hk
    rw [hzero _ (by omega), Nat.zero_div, Nat.zero_mod]

theorem fastLimbs_congr {a b : ByteArray} {ptr count : Nat}
    (h : ∀ j, j < count →
      MachineState.readWord a (ptr + 32 * j) = MachineState.readWord b (ptr + 32 * j)) :
    fastLimbs a ptr count = fastLimbs b ptr count := by
  unfold fastLimbs
  apply List.map_congr_left
  intro k hk
  have hk' : k < count := by simpa using hk
  rw [h _ (by omega)]

/-- Representation depends only on the words of the block. -/
theorem fastRepresents_congr {a b : ByteArray} {ptr count : Nat}
    (h : ∀ j, j < count →
      MachineState.readWord a (ptr + 32 * j) = MachineState.readWord b (ptr + 32 * j))
    (value : Nat) :
    FastRepresents a ptr count value ↔ FastRepresents b ptr count value := by
  unfold FastRepresents
  rw [fastLimbs_congr h]

/-- Representation depends only on the bytes of the block. -/
theorem fastRepresents_congr_bytes {a b : ByteArray} {ptr count : Nat}
    (h : ∀ i, i < 32 * count → a[ptr + i]?.getD 0 = b[ptr + i]?.getD 0)
    (value : Nat) :
    FastRepresents a ptr count value ↔ FastRepresents b ptr count value := by
  apply fastRepresents_congr
  intro j hj
  unfold MachineState.readWord
  rw [Challenge.EvmProof.Memory.readPadded_congr a b (ptr + 32 * j) 32]
  intro i hi
  have := h (32 * j + i) (by omega)
  rwa [← Nat.add_assoc] at this

/-- Writing outside the block preserves the representation. -/
theorem fastRepresents_writeBytes_disjoint (memory bytes : ByteArray)
    (dst ptr count value : Nat)
    (hdisjoint : dst + bytes.size ≤ ptr ∨ ptr + 32 * count ≤ dst)
    (hrep : FastRepresents memory ptr count value) :
    FastRepresents (MachineState.writeBytes memory bytes dst) ptr count value := by
  refine (fastRepresents_congr ?_ value).2 hrep
  intro j hj
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rcases hdisjoint with hbefore | hafter
  · right
    omega
  · left
    omega

/-- Writing a word outside the block preserves the representation. -/
theorem fastRepresents_writeWord_disjoint (memory : ByteArray)
    (dst ptr count value word : Nat)
    (hdisjoint : dst + 32 ≤ ptr ∨ ptr + 32 * count ≤ dst)
    (hrep : FastRepresents memory ptr count value) :
    FastRepresents
      (MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word 32) dst)
      ptr count value := by
  apply fastRepresents_writeBytes_disjoint memory _ dst ptr count value _ hrep
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  exact hdisjoint

/-- Writing limb `k` (from the least significant) updates exactly that entry
of the limb list. -/
theorem fastLimbs_write_at (memory : ByteArray) (ptr count k : Nat)
    (word : UInt256) (hk : k < count) :
    fastLimbs
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded word.toNat 32) (ptr + 32 * (count - 1 - k)))
        ptr count =
      (fastLimbs memory ptr count).set k word.toNat := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have hjc : j < count := by simpa using hj
    rw [List.getElem_set]
    split
    · next heq =>
      subst heq
      rw [fastLimbs_getElem, Challenge.EvmProof.Memory.readWord_writeWord]
    · next hne =>
      rw [fastLimbs_getElem, fastLimbs_getElem,
        Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · first
          | (right; omega)
          | (left; omega)
      · first
          | (left; omega)
          | (right; omega)

/-- Replacing one digit of a radix expansion. -/
theorem ofDigits_set (base : Nat) (digits : List Nat) (k w : Nat)
    (hk : k < digits.length) :
    Nat.ofDigits base (digits.set k w) + digits[k] * base ^ k =
      Nat.ofDigits base digits + w * base ^ k := by
  induction digits generalizing k with
  | nil => simp at hk
  | cons d digits ih =>
      cases k with
      | zero => simp [Nat.ofDigits_cons]; ring
      | succ k =>
          have hk' : k < digits.length := by simpa using hk
          have ih' := ih k hk'
          simp only [List.set_cons_succ, List.getElem_cons_succ, Nat.ofDigits_cons,
            pow_succ]
          have h2 : base * (Nat.ofDigits base (digits.set k w) + digits[k] * base ^ k) =
              base * (Nat.ofDigits base digits + w * base ^ k) := by rw [ih']
          nlinarith [h2]

/-- Writing limb `k` of a represented block: the new value replaces digit `k`. -/
theorem fastRepresents_write_limb {memory : ByteArray} {ptr count value k value' : Nat}
    (word : UInt256) (hrep : FastRepresents memory ptr count value) (hk : k < count)
    (hvalue' : value' + value / Limbs.radix ^ k % Limbs.radix * Limbs.radix ^ k =
      value + word.toNat * Limbs.radix ^ k) :
    FastRepresents
      (MachineState.writeBytes memory
        (Data.Bytes.natToBytesPadded word.toNat 32) (ptr + 32 * (count - 1 - k)))
      ptr count value' := by
  have hlen : k < (fastLimbs memory ptr count).length := by simpa using hk
  have hdigit : (fastLimbs memory ptr count)[k] = value / Limbs.radix ^ k % Limbs.radix := by
    rw [getElem_eq_div_mod_ofDigits _ k hlen (fun d hd => fastLimb_lt memory ptr count hd),
      value_of_fastRepresents hrep]
  have hset := ofDigits_set Limbs.radix (fastLimbs memory ptr count) k word.toNat hlen
  rw [hdigit, value_of_fastRepresents hrep] at hset
  have hval : Nat.ofDigits Limbs.radix ((fastLimbs memory ptr count).set k word.toNat) =
      value' := by omega
  have hdigits : ∀ d ∈ (fastLimbs memory ptr count).set k word.toNat, d < Limbs.radix := by
    intro d hd
    rcases List.mem_or_eq_of_mem_set hd with hmem | rfl
    · exact fastLimb_lt memory ptr count hmem
    · exact word.val.isLt
  have hlt : value' < Limbs.radix ^ count := by
    have := Nat.ofDigits_lt_base_pow_length Limbs.radix_gt_one hdigits
    rwa [hval, List.length_set, length_fastLimbs] at this
  refine (fastRepresents_iff_value hlt).2 ?_
  rw [fastLimbs_write_at memory ptr count k word hk, hval]

/-- Writing into a zero limb adds `word * radix ^ k`. -/
theorem fastRepresents_write_zero_limb {memory : ByteArray} {ptr count value k : Nat}
    (word : UInt256) (hrep : FastRepresents memory ptr count value) (hk : k < count)
    (hzero : value / Limbs.radix ^ k % Limbs.radix = 0) :
    FastRepresents
      (MachineState.writeBytes memory
        (Data.Bytes.natToBytesPadded word.toNat 32) (ptr + 32 * (count - 1 - k)))
      ptr count (value + word.toNat * Limbs.radix ^ k) := by
  apply fastRepresents_write_limb word hrep hk
  rw [hzero, Nat.zero_mul, Nat.add_zero]

/-- Writing the least significant limb of a zero block. -/
theorem fastRepresents_write_low_of_zero {memory : ByteArray} {ptr count : Nat}
    (word : UInt256) (hrep : FastRepresents memory ptr count 0) (hcount : 0 < count) :
    FastRepresents
      (MachineState.writeBytes memory
        (Data.Bytes.natToBytesPadded word.toNat 32) (ptr + 32 * (count - 1)))
      ptr count word.toNat := by
  have h := fastRepresents_write_zero_limb (k := 0) word hrep hcount (by simp)
  simpa using h

/-- Writing the most significant limb of a zero block. -/
theorem fastRepresents_write_high_of_zero {memory : ByteArray} {ptr count : Nat}
    (word : UInt256) (hrep : FastRepresents memory ptr count 0) (hcount : 0 < count) :
    FastRepresents
      (MachineState.writeBytes memory
        (Data.Bytes.natToBytesPadded word.toNat 32) ptr)
      ptr count (word.toNat * Limbs.radix ^ (count - 1)) := by
  have h := fastRepresents_write_zero_limb (k := count - 1) word hrep (by omega) (by simp)
  rwa [Nat.sub_self, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at h

/-! ## Arithmetic facts about the modulus -/

theorem two_dvd_radix : 2 ∣ Limbs.radix := by
  rw [Limbs.radix, pow_succ]
  exact Dvd.intro_left _ rfl

theorem coprime_two_of_odd {m : Nat} (hodd : m % 2 = 1) : Nat.Coprime 2 m := by
  rw [Nat.Coprime, Nat.gcd_rec, hodd]
  rfl

theorem coprime_radix_of_odd {m : Nat} (hodd : m % 2 = 1) :
    Nat.Coprime Limbs.radix m := by
  rw [Limbs.radix]
  exact (coprime_two_of_odd hodd).pow_left 256

theorem coprime_radix_pow_of_odd {m : Nat} (hodd : m % 2 = 1) (n : Nat) :
    Nat.Coprime (Limbs.radix ^ n) m :=
  (coprime_radix_of_odd hodd).pow_left n

theorem low_limb_odd {m : Nat} (hodd : m % 2 = 1) : m % Limbs.radix % 2 = 1 := by
  rw [Nat.mod_mod_of_dvd m two_dvd_radix]
  exact hodd

/-- P3 and P4: an odd modulus with a nonzero top limb strictly exceeds
`radix ^ (n - 1)`. -/
theorem radix_pow_lt_of_odd {m n : Nat} (hn : 2 ≤ n)
    (hm : Limbs.radix ^ (n - 1) ≤ m) (hodd : m % 2 = 1) :
    Limbs.radix ^ (n - 1) < m := by
  rcases Nat.lt_or_eq_of_le hm with hlt | heq
  · exact hlt
  · exfalso
    have h2 : 2 ∣ Limbs.radix ^ (n - 1) := dvd_pow two_dvd_radix (by omega)
    rw [heq] at h2
    omega

/-! ## Montgomery multiplication -/

/-- Montgomery product: the residue `x * y * R⁻¹ mod m`. -/
def montMul (m R x y : Nat) : Nat :=
  ((x : ZMod m) * (y : ZMod m) * (R : ZMod m)⁻¹).val

theorem montMul_lt {m : Nat} (hm : 0 < m) (R x y : Nat) : montMul m R x y < m := by
  haveI : NeZero m := ⟨hm.ne'⟩
  exact ZMod.val_lt _

/-- The defining congruence of the Montgomery product. -/
theorem montMul_mul_R_modEq {m R : Nat} (hm : 0 < m) (hcop : Nat.Coprime R m)
    (x y : Nat) : montMul m R x y * R ≡ x * y [MOD m] := by
  haveI : NeZero m := ⟨hm.ne'⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  unfold montMul
  rw [ZMod.natCast_zmod_val]
  have h1 : (R : ZMod m) * (R : ZMod m)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one R hcop
  calc (x : ZMod m) * y * (R : ZMod m)⁻¹ * R
      = x * y * ((R : ZMod m) * (R : ZMod m)⁻¹) := by ring
    _ = x * y := by rw [h1, mul_one]

/-- Uniqueness: any `z < m` with `z * R ≡ x * y` is the Montgomery product. -/
theorem montMul_eq_of_modEq {m R x y z : Nat} (hm : 0 < m) (hcop : Nat.Coprime R m)
    (hz : z * R ≡ x * y [MOD m]) (hzlt : z < m) : montMul m R x y = z := by
  have hmne : m ≠ 0 := Nat.ne_of_gt hm
  haveI : NeZero m := ⟨hmne⟩
  have h1 : (R : ZMod m) * (R : ZMod m)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one R hcop
  have hz' : ((z * R : Nat) : ZMod m) = ((x * y : Nat) : ZMod m) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hz
  push_cast at hz'
  unfold montMul
  rw [← hz']
  calc ((z : ZMod m) * R * (R : ZMod m)⁻¹).val
      = ((z : ZMod m) * ((R : ZMod m) * (R : ZMod m)⁻¹)).val := by rw [mul_assoc]
    _ = (z : ZMod m).val := by rw [h1, mul_one]
    _ = z := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hzlt]

/-- The shape a CIOS loop produces: `z * R = x * y + q * m`. -/
theorem montMul_eq_of_mul_eq {m R x y z q : Nat} (hm : 0 < m) (hcop : Nat.Coprime R m)
    (hz : z * R = x * y + q * m) (hzlt : z < m) : montMul m R x y = z := by
  apply montMul_eq_of_modEq hm hcop _ hzlt
  unfold Nat.ModEq
  rw [hz, Nat.add_mul_mod_self_right]

/-- After the final conditional subtraction, `t mod m` is the product. -/
theorem montMul_eq_mod_of_mul_eq {m R x y t q : Nat} (hm : 0 < m) (hcop : Nat.Coprime R m)
    (ht : t * R = x * y + q * m) : montMul m R x y = t % m := by
  apply montMul_eq_of_modEq hm hcop _ (Nat.mod_lt _ hm)
  calc t % m * R ≡ t * R [MOD m] := (Nat.mod_modEq _ _).mul_right R
    _ = x * y + q * m := ht
    _ ≡ x * y [MOD m] := by
        unfold Nat.ModEq
        rw [Nat.add_mul_mod_self_right]

/-- Exact-division form: `montMul = (x * y + q * m) / R`. -/
theorem montMul_eq_div {m R x y q : Nat} (hm : 0 < m) (hcop : Nat.Coprime R m)
    (hdiv : R ∣ x * y + q * m) (hlt : (x * y + q * m) / R < m) :
    montMul m R x y = (x * y + q * m) / R :=
  montMul_eq_of_mul_eq hm hcop (Nat.div_mul_cancel hdiv) hlt

/-- Montgomery form is multiplicative: `φ(x) ⊗ φ(y) = φ(x * y)`. -/
theorem montMul_form {m R x y x' y' : Nat} (hm : 0 < m) (hcop : Nat.Coprime R m)
    (hx : x' ≡ x * R [MOD m]) (hy : y' ≡ y * R [MOD m]) :
    montMul m R x' y' = x * y * R % m := by
  apply montMul_eq_of_modEq hm hcop _ (Nat.mod_lt _ hm)
  calc x * y * R % m * R ≡ x * y * R * R [MOD m] := (Nat.mod_modEq _ _).mul_right R
    _ = (x * R) * (y * R) := by ring
    _ ≡ x' * y' [MOD m] := hx.symm.mul hy.symm

/-- Multiplying by a constant given in Montgomery form: `x ⊗ φ(c) = x * c`. -/
theorem montMul_const_form {m R c c' : Nat} (hm : 0 < m) (hcop : Nat.Coprime R m)
    (hc : c' ≡ c * R [MOD m]) (x : Nat) :
    montMul m R x c' = x * c % m := by
  apply montMul_eq_of_modEq hm hcop _ (Nat.mod_lt _ hm)
  calc x * c % m * R ≡ x * c * R [MOD m] := (Nat.mod_modEq _ _).mul_right R
    _ = x * (c * R) := by ring
    _ ≡ x * c' [MOD m] := hc.symm.mul_left x

/-- Conversion in: multiplying by `R² mod m` produces the Montgomery form. -/
theorem montMul_R_sq {m R : Nat} (hm : 0 < m) (hcop : Nat.Coprime R m) (x : Nat) :
    montMul m R x (R * R % m) = x * R % m :=
  montMul_const_form hm hcop (Nat.mod_modEq _ _) x

/-- Conversion out: multiplying a Montgomery form by `1` recovers the value. -/
theorem montMul_one_of_form {m R x x' : Nat} (hm : 0 < m) (hcop : Nat.Coprime R m)
    (hx : x' ≡ x * R [MOD m]) : montMul m R x' 1 = x % m := by
  apply montMul_eq_of_modEq hm hcop _ (Nat.mod_lt _ hm)
  calc x % m * R ≡ x * R [MOD m] := (Nat.mod_modEq _ _).mul_right R
    _ ≡ x' [MOD m] := hx.symm
    _ = x' * 1 := (mul_one _).symm

theorem montMul_one_eq {m R x : Nat} (hm : 0 < m) (hcop : Nat.Coprime R m) (hx : x < m) :
    montMul m R (x * R % m) 1 = x := by
  rw [montMul_one_of_form hm hcop (Nat.mod_modEq _ _), Nat.mod_eq_of_lt hx]

/-! ## The CIOS row -/

/-- The `mu` choice makes the row sum divisible by the radix: `u` is any
number congruent to the current low limb `t + a * bi`, and `minv` satisfies
`m * minv ≡ -1`. -/
theorem cios_mu_dvd {β m minv u t a bi : Nat}
    (hminv : (m * minv + 1) % β = 0) (hu : u % β = (t + a * bi) % β) :
    β ∣ t + a * bi + u * minv % β * m := by
  apply Nat.modEq_zero_iff_dvd.1
  have h1 : t + a * bi ≡ u [MOD β] := hu.symm
  have h2 : u * minv % β ≡ u * minv [MOD β] := Nat.mod_modEq _ _
  have h3 : m * minv + 1 ≡ 0 [MOD β] := by
    unfold Nat.ModEq
    rw [hminv, Nat.zero_mod]
  calc t + a * bi + u * minv % β * m ≡ u + u * minv * m [MOD β] := h1.add (h2.mul_right m)
    _ = u * (m * minv + 1) := by ring
    _ ≡ u * 0 [MOD β] := h3.mul_left u
    _ = 0 := by ring

/-- `minv` only depends on the low limb of the modulus. -/
theorem minv_of_low_limb {β m minv : Nat} (h : (m % β * minv + 1) % β = 0) :
    (m * minv + 1) % β = 0 := by
  have hcongr : m * minv + 1 ≡ m % β * minv + 1 [MOD β] :=
    ((Nat.mod_modEq m β).symm.mul_right minv).add_right 1
  rw [hcongr]
  exact h

/-- Negating an inverse: from `m * x ≡ 1` to `m * (β - x) + 1 ≡ 0`. -/
theorem negInv_spec {β m x : Nat} (hβ : 1 < β) (hx : m * x % β = 1) (hxβ : x ≤ β) :
    (m * (β - x) + 1) % β = 0 := by
  have hone : (1 : Nat) ≡ m * x [MOD β] := by
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hβ, hx]
  have hsum : m * (β - x) + m * x = m * β := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hxβ]
  have hstep : (m * (β - x) + 1) % β = (m * (β - x) + m * x) % β :=
    hone.add_left (m * (β - x))
  rw [hstep, hsum, Nat.mul_mod_left]

/-- Bound for one CIOS row: the new partial product stays below `2m`. -/
theorem cios_bound {m β a bi t mu : Nat} (hβ : 0 < β)
    (ha : a < m) (hbi : bi < β) (ht : t < 2 * m) (hmu : mu < β) :
    (t + a * bi + mu * m) / β < 2 * m := by
  rw [Nat.div_lt_iff_lt_mul hβ]
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_lt ha
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hbi
  have hmu' : mu * (a + a' + 1) ≤ (bi + k) * (a + a' + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  nlinarith [hmu']

/-- Tighter bound used by the plan: `t < a + m` is preserved. -/
theorem cios_bound_tight {m β a bi t mu : Nat} (hβ : 0 < β)
    (hbi : bi < β) (ht : t < a + m) (hmu : mu < β) :
    (t + a * bi + mu * m) / β < a + m := by
  rw [Nat.div_lt_iff_lt_mul hβ]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hbi
  have hmu' : mu * m ≤ (bi + k) * m := Nat.mul_le_mul_right _ (by omega)
  nlinarith [hmu']

/-- One CIOS row.  From the invariant `t * β ^ i = a * bpre + Q * m`, where
`bpre` is the value of the `i` consumed limbs of `b`, and a `mu` making the
row sum divisible by `β`, the next partial product `t' = (t + a*bi + mu*m)/β`
satisfies the invariant with one more limb and stays below `2m`. -/
theorem cios_step {m β a bpre bi t Q mu i : Nat} (hβ : 0 < β)
    (ha : a < m) (hbi : bi < β) (ht : t < 2 * m) (hmu : mu < β)
    (hinv : t * β ^ i = a * bpre + Q * m)
    (hdiv : β ∣ t + a * bi + mu * m) :
    (t + a * bi + mu * m) / β * β ^ (i + 1) =
        a * (bpre + bi * β ^ i) + (Q + mu * β ^ i) * m ∧
      (t + a * bi + mu * m) / β < 2 * m := by
  refine ⟨?_, cios_bound hβ ha hbi ht hmu⟩
  have hexact : (t + a * bi + mu * m) / β * β = t + a * bi + mu * m :=
    Nat.div_mul_cancel hdiv
  calc (t + a * bi + mu * m) / β * β ^ (i + 1)
      = (t + a * bi + mu * m) / β * β * β ^ i := by ring
    _ = (t + a * bi + mu * m) * β ^ i := by rw [hexact]
    _ = t * β ^ i + (a * bi + mu * m) * β ^ i := by ring
    _ = a * bpre + Q * m + (a * bi + mu * m) * β ^ i := by rw [hinv]
    _ = a * (bpre + bi * β ^ i) + (Q + mu * β ^ i) * m := by ring

/-- The exact row equation without the bound, for invariants that track the
partial product as a limb string. -/
theorem cios_row_eq {β s : Nat} (hdiv : β ∣ s) : s / β * β = s :=
  Nat.div_mul_cancel hdiv

/-- Conditional subtraction after the last row. -/
theorem mod_eq_cond_sub_of_lt_twice {t m : Nat} (ht : t < 2 * m) :
    t % m = if t < m then t else t - m :=
  Limbs.mod_eq_cond_sub ht

/-! ## Modular doubling chains -/

/-- `k` modular doublings of `x`. -/
def doubleChain (m x : Nat) : Nat → Nat
  | 0 => x
  | k + 1 => (doubleChain m x k + doubleChain m x k) % m

@[simp] theorem doubleChain_zero (m x : Nat) : doubleChain m x 0 = x := rfl

theorem doubleChain_succ (m x k : Nat) :
    doubleChain m x (k + 1) = (doubleChain m x k + doubleChain m x k) % m := rfl

theorem doubleChain_add (m x j k : Nat) :
    doubleChain m x (j + k) = doubleChain m (doubleChain m x j) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, doubleChain_succ, ih, doubleChain_succ]

theorem doubleChain_lt {m x : Nat} (hm : 0 < m) (hx : x < m) (k : Nat) :
    doubleChain m x k < m := by
  cases k with
  | zero => exact hx
  | succ k => exact Nat.mod_lt _ hm

theorem doubleChain_eq {m x : Nat} (hx : x < m) (k : Nat) :
    doubleChain m x k = x * 2 ^ k % m := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt hx]
  | succ k ih =>
      rw [doubleChain_succ, ih, ← Nat.add_mod]
      congr 1
      ring

/-- One doubling step is an `ADDMOD` of a value with itself. -/
theorem double_mod_eq_cond_sub {m x : Nat} (hx : x < m) :
    (x + x) % m = if x + x < m then x + x else x + x - m :=
  Limbs.mod_eq_cond_sub (by omega)

/-- 256 doublings multiply by the radix. -/
theorem doubleChain_256 {m x : Nat} (hx : x < m) :
    doubleChain m x 256 = x * Limbs.radix % m :=
  doubleChain_eq hx 256

theorem doubleChain_mul_256 {m x : Nat} (hx : x < m) (n : Nat) :
    doubleChain m x (256 * n) = x * Limbs.radix ^ n % m := by
  rw [doubleChain_eq hx, Limbs.radix, ← pow_mul]

/-- The `R1` construction: doubling `radix ^ (n - 1)` 256 times gives `R mod m`. -/
theorem doubleChain_R1 {m n : Nat} (hn : 1 ≤ n) (hx : Limbs.radix ^ (n - 1) < m) :
    doubleChain m (Limbs.radix ^ (n - 1)) 256 = Limbs.radix ^ n % m := by
  rw [doubleChain_256 hx, ← pow_succ, Nat.sub_add_cancel hn]

/-- The `CC` construction: doubling `R mod m` 256 times gives `radix * R mod m`. -/
theorem doubleChain_CC {m R : Nat} (hm : 0 < m) :
    doubleChain m (R % m) 256 = Limbs.radix * R % m := by
  rw [doubleChain_256 (Nat.mod_lt _ hm), Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
    Nat.mul_comm]

/-! ## Horner base reduction -/

/-- One Horner step: shift in a limb and reduce. -/
def hornerStep (m r limb : Nat) : Nat := (r * Limbs.radix + limb) % m

/-- Horner reduction of a most-significant-first limb list. -/
def hornerMod (m : Nat) (limbs : List Nat) : Nat := limbs.foldl (hornerStep m) 0

theorem hornerMod_nil (m : Nat) : hornerMod m [] = 0 := rfl

theorem foldl_hornerStep_append (m r : Nat) (limbs : List Nat) (limb : Nat) :
    (limbs ++ [limb]).foldl (hornerStep m) r =
      (limbs.foldl (hornerStep m) r * Limbs.radix + limb) % m := by
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

theorem hornerMod_append (m : Nat) (limbs : List Nat) (limb : Nat) :
    hornerMod m (limbs ++ [limb]) = (hornerMod m limbs * Limbs.radix + limb) % m :=
  foldl_hornerStep_append m 0 limbs limb

theorem foldl_hornerStep {m r : Nat} (hm : 0 < m) (hr : r < m) (limbs : List Nat) :
    limbs.foldl (hornerStep m) r =
      (r * Limbs.radix ^ limbs.length + Nat.ofDigits Limbs.radix limbs.reverse) % m := by
  induction limbs generalizing r with
  | nil => simp [Nat.mod_eq_of_lt hr]
  | cons d limbs ih =>
      rw [List.foldl_cons, hornerStep, ih (Nat.mod_lt _ hm), List.reverse_cons,
        Nat.ofDigits_append, List.length_reverse, List.length_cons,
        Nat.ofDigits_singleton]
      have h : ((r * Limbs.radix + d) % m * Limbs.radix ^ limbs.length +
            Nat.ofDigits Limbs.radix limbs.reverse) % m =
          ((r * Limbs.radix + d) * Limbs.radix ^ limbs.length +
            Nat.ofDigits Limbs.radix limbs.reverse) % m :=
        ((Nat.mod_modEq _ _).mul_right _).add_right _
      rw [h]
      congr 1
      ring

/-- Horner reduction computes the value of the limb list modulo `m`. -/
theorem hornerMod_eq {m : Nat} (hm : 0 < m) (limbs : List Nat) :
    hornerMod m limbs = Nat.ofDigits Limbs.radix limbs.reverse % m := by
  unfold hornerMod
  rw [foldl_hornerStep hm hm limbs, Nat.zero_mul, Nat.zero_add]

/-- Folding over the limbs of a represented block (in address order, i.e. most
significant first) yields the value modulo `m`. -/
theorem hornerMod_of_fastRepresents {memory : ByteArray} {ptr count value m : Nat}
    (hm : 0 < m) (hrep : FastRepresents memory ptr count value) :
    hornerMod m (Limbs.memoryLimbs memory ptr count) = value % m := by
  rw [hornerMod_eq hm, memoryLimbs_eq_reverse_fastLimbs, List.reverse_reverse,
    value_of_fastRepresents hrep]

/-- Horner in quotient form: consuming limb `k` of `b` (from the least
significant) moves the accumulator from `⌊b / radix^(k+1)⌋ mod m` to
`⌊b / radix^k⌋ mod m`. -/
theorem horner_div_step (m b k : Nat) :
    (b / Limbs.radix ^ (k + 1) % m * Limbs.radix % m + b / Limbs.radix ^ k % Limbs.radix) % m =
      b / Limbs.radix ^ k % m := by
  have hsplit : b / Limbs.radix ^ (k + 1) * Limbs.radix + b / Limbs.radix ^ k % Limbs.radix =
      b / Limbs.radix ^ k := by
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
    exact Nat.div_add_mod' _ _
  calc (b / Limbs.radix ^ (k + 1) % m * Limbs.radix % m +
        b / Limbs.radix ^ k % Limbs.radix) % m
      = (b / Limbs.radix ^ (k + 1) * Limbs.radix +
          b / Limbs.radix ^ k % Limbs.radix) % m :=
        ((Nat.mod_modEq _ _).trans ((Nat.mod_modEq _ _).mul_right _)).add_right _
    _ = b / Limbs.radix ^ k % m := by rw [hsplit]

theorem div_pow_lt_of_lt {b k B : Nat} (hb : b < Limbs.radix ^ B) (hk : B ≤ k) :
    b / Limbs.radix ^ k = 0 := by
  apply Nat.div_eq_of_lt
  exact hb.trans_le (Nat.pow_le_pow_right Limbs.radix_pos hk)

theorem div_pow_zero (b : Nat) : b / Limbs.radix ^ 0 = b := by
  simp

/-! ## Left-to-right square-and-multiply -/

/-- The exponent formed by the bits of `e` above position `j`: the prefix a
left-to-right scan has consumed once it reaches bit `j`. -/
def expPrefix (e j : Nat) : Nat := e / 2 ^ j

@[simp] theorem expPrefix_zero (e : Nat) : expPrefix e 0 = e := by
  simp [expPrefix]

theorem expPrefix_top {e B : Nat} (he : e < 2 ^ B) : expPrefix e B = 0 :=
  Nat.div_eq_of_lt he

theorem expPrefix_of_le {e B j : Nat} (he : e < 2 ^ B) (hj : B ≤ j) : expPrefix e j = 0 :=
  Nat.div_eq_of_lt (he.trans_le (Nat.pow_le_pow_right (by norm_num) hj))

/-- Consuming bit `j` doubles the prefix and adds the bit. -/
theorem expPrefix_succ (e j : Nat) :
    expPrefix e j = 2 * expPrefix e (j + 1) + e / 2 ^ j % 2 := by
  unfold expPrefix
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  exact (Nat.div_add_mod (e / 2 ^ j) 2).symm

theorem expPrefix_eq_shiftRight (e j : Nat) : expPrefix e j = e >>> j := by
  rw [expPrefix, Nat.shiftRight_eq_div_pow]

theorem bit_eq_testBit (e j : Nat) : e / 2 ^ j % 2 = (e.testBit j).toNat :=
  (Nat.toNat_testBit e j).symm

theorem sq_step {m b E acc : Nat} (hacc : acc = b ^ E % m) :
    acc * acc % m = b ^ (2 * E) % m := by
  rw [hacc, ← Nat.mul_mod, ← pow_add, two_mul]

theorem mul_step {m b E acc : Nat} (hacc : acc = b ^ E % m) :
    acc * b % m = b ^ (E + 1) % m := by
  rw [hacc, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, pow_succ]

theorem mul_step_of_modEq {m b b' E acc : Nat} (hacc : acc = b ^ E % m)
    (hb : b' ≡ b [MOD m]) : acc * b' % m = b ^ (E + 1) % m := by
  rw [hacc, pow_succ]
  exact ((Nat.mod_modEq _ _).mul hb)

/-- Squaring in Montgomery form. -/
theorem mont_sq_step {m R b E acc : Nat} (hm : 0 < m) (hcop : Nat.Coprime R m)
    (hacc : acc ≡ b ^ E * R [MOD m]) :
    montMul m R acc acc = b ^ (2 * E) * R % m := by
  rw [montMul_form hm hcop hacc hacc, ← pow_add, two_mul]

/-- Multiplying by the Montgomery form of the base. -/
theorem mont_mul_step {m R b bM E acc : Nat} (hm : 0 < m) (hcop : Nat.Coprime R m)
    (hacc : acc ≡ b ^ E * R [MOD m]) (hb : bM ≡ b * R [MOD m]) :
    montMul m R acc bM = b ^ (E + 1) * R % m := by
  rw [montMul_form hm hcop hacc hb, pow_succ]

/-- One left-to-right bit: square, then multiply if the bit is set. -/
theorem mont_bit_step {m R b bM E acc bit : Nat} (hm : 0 < m) (hcop : Nat.Coprime R m)
    (hacc : acc ≡ b ^ E * R [MOD m]) (hb : bM ≡ b * R [MOD m]) (hbit : bit ≤ 1) :
    (if bit = 0 then montMul m R acc acc
      else montMul m R (montMul m R acc acc) bM) = b ^ (2 * E + bit) * R % m := by
  have hsq := mont_sq_step hm hcop hacc
  split
  · next h0 => rw [hsq, h0, Nat.add_zero]
  · next h1 =>
      have hbit1 : bit = 1 := by omega
      rw [mont_mul_step hm hcop (b := b) (E := 2 * E) _ hb, hbit1]
      rw [hsq]
      exact Nat.mod_modEq _ _

/-- Converting the accumulator out of Montgomery form. -/
theorem mont_out {m R b e acc : Nat} (hm : 0 < m) (hcop : Nat.Coprime R m)
    (hacc : acc ≡ b ^ e * R [MOD m]) : montMul m R acc 1 = b ^ e % m :=
  montMul_one_of_form hm hcop hacc

/-- The Montgomery form of `1` is `R mod m`, the start of the exponent loop. -/
theorem mont_one_form (m R : Nat) : R % m ≡ 1 ^ 0 * R [MOD m] := by
  rw [pow_zero, one_mul]
  exact Nat.mod_modEq _ _

theorem mont_pow_zero_form (m R b : Nat) : R % m ≡ b ^ 0 * R [MOD m] := by
  rw [pow_zero, one_mul]
  exact Nat.mod_modEq _ _

/-- The reference precompile is ordinary modular exponentiation. -/
theorem modPow_eq_pow_mod {m : Nat} (hm : 0 < m) (b e : Nat) :
    EVM.Precompile.modPow b e m = b ^ e % m := by
  rw [Algorithm.modPow_eq, if_neg hm.ne']

/-- Endpoint of the exponent loop: the accumulator in Montgomery form for the
whole exponent converts to the precompile's answer. -/
theorem mont_out_modPow {m R b e acc : Nat} (hm : 0 < m) (hcop : Nat.Coprime R m)
    (hacc : acc ≡ b ^ e * R [MOD m]) :
    montMul m R acc 1 = EVM.Precompile.modPow b e m := by
  rw [mont_out hm hcop hacc, modPow_eq_pow_mod hm]

/-! ## Newton iteration for the inverse modulo `2^256` -/

/-- One Newton step `x ↦ x * (2 - m * x)` with the EVM's wrapping arithmetic. -/
def newtonStep (m x : Nat) : Nat :=
  x * ((2 + Limbs.radix - m * x % Limbs.radix) % Limbs.radix) % Limbs.radix

/-- `j` Newton steps starting from `1`. -/
def newtonIter (m : Nat) : Nat → Nat
  | 0 => 1
  | j + 1 => newtonStep m (newtonIter m j)

theorem newtonIter_succ (m j : Nat) :
    newtonIter m (j + 1) = newtonStep m (newtonIter m j) := rfl

theorem newtonStep_lt (m x : Nat) : newtonStep m x < Limbs.radix :=
  Nat.mod_lt _ Limbs.radix_pos

theorem radix_int : ((Limbs.radix : Nat) : Int) = (2 : Int) ^ 256 := by
  rw [Limbs.radix]
  push_cast

/-- The wrapped step agrees with the integer Newton step modulo `2^256`. -/
theorem newtonStep_modEq (m x : Nat) :
    ((newtonStep m x : Nat) : Int) ≡ (x : Int) * (2 - (m : Int) * x) [ZMOD (2 : Int) ^ 256] := by
  unfold newtonStep
  have hr : m * x % Limbs.radix ≤ 2 + Limbs.radix := by
    have := Nat.mod_lt (m * x) Limbs.radix_pos
    omega
  push_cast [Nat.cast_sub hr]
  rw [radix_int]
  have h0 : (2 : Int) ^ 256 ≡ 0 [ZMOD (2 : Int) ^ 256] := Int.modEq_zero_iff_dvd.2 dvd_rfl
  have hmx : (m : Int) * x % (2 : Int) ^ 256 ≡ m * x [ZMOD (2 : Int) ^ 256] :=
    Int.mod_modEq _ _
  calc (x : Int) * ((2 + (2 : Int) ^ 256 - (m : Int) * x % (2 : Int) ^ 256) % (2 : Int) ^ 256) %
        (2 : Int) ^ 256
      ≡ x * ((2 + (2 : Int) ^ 256 - (m : Int) * x % (2 : Int) ^ 256) % (2 : Int) ^ 256)
          [ZMOD (2 : Int) ^ 256] := Int.mod_modEq _ _
    _ ≡ x * (2 + (2 : Int) ^ 256 - (m : Int) * x % (2 : Int) ^ 256) [ZMOD (2 : Int) ^ 256] :=
        (Int.mod_modEq _ _).mul_left x
    _ ≡ x * (2 + 0 - (m : Int) * x) [ZMOD (2 : Int) ^ 256] :=
        ((h0.add_left 2).sub hmx).mul_left x
    _ = x * (2 - (m : Int) * x) := by ring

/-- Newton doubles the precision: `k` correct bits become `2k` bits, as long as
`2k` bits fit in a word. -/
theorem newton_step_int {m x y : Int} {k : Nat} (hk : 2 * k ≤ 256)
    (hx : (2 : Int) ^ k ∣ m * x - 1)
    (hy : y ≡ x * (2 - m * x) [ZMOD (2 : Int) ^ 256]) :
    (2 : Int) ^ (2 * k) ∣ m * y - 1 := by
  have hdvd : (2 : Int) ^ (2 * k) ∣ (2 : Int) ^ 256 := pow_dvd_pow 2 hk
  have hy' : y ≡ x * (2 - m * x) [ZMOD (2 : Int) ^ (2 * k)] := hy.of_dvd hdvd
  have h1 : (2 : Int) ^ (2 * k) ∣ (m * x - 1) ^ 2 := by
    rw [Nat.mul_comm 2 k, pow_mul]
    exact pow_dvd_pow_of_dvd hx 2
  have h2 : (2 : Int) ^ (2 * k) ∣ m * (x * (2 - m * x)) - 1 := by
    have heq : m * (x * (2 - m * x)) - 1 = -((m * x - 1) ^ 2) := by ring
    rw [heq]
    exact (dvd_neg).2 h1
  have h3 : m * (x * (2 - m * x)) - 1 ≡ m * y - 1 [ZMOD (2 : Int) ^ (2 * k)] :=
    (hy'.symm.mul_left m).sub_right 1
  have h4 := dvd_add h3.dvd h2
  simpa using h4

/-- The same statement over `Nat`. -/
theorem newton_step_nat {m x y k : Nat} (hk : 2 * k ≤ 256)
    (hx : m * x % 2 ^ k = 1 % 2 ^ k)
    (hy : (y : Int) ≡ (x : Int) * (2 - (m : Int) * x) [ZMOD (2 : Int) ^ 256]) :
    m * y % 2 ^ (2 * k) = 1 % 2 ^ (2 * k) := by
  have hx' : (1 : Int) ≡ ((m * x : Nat) : Int) [ZMOD ((2 ^ k : Nat) : Int)] := by
    rw [show (1 : Int) = ((1 : Nat) : Int) by rfl, Int.natCast_modEq_iff]
    exact hx.symm
  rw [Int.modEq_iff_dvd] at hx'
  push_cast at hx'
  have hy' := newton_step_int hk hx' hy
  have hresult : ((1 : Nat) : Int) ≡ ((m * y : Nat) : Int)
      [ZMOD ((2 ^ (2 * k) : Nat) : Int)] := by
    rw [Int.modEq_iff_dvd]
    push_cast
    exact hy'
  rw [Int.natCast_modEq_iff] at hresult
  exact hresult.symm

/-- After `j ≤ 8` Newton steps from `1`, `m * x ≡ 1` modulo `2 ^ (2 ^ j)`. -/
theorem newtonIter_spec {m : Nat} (hodd : m % 2 = 1) :
    ∀ j, j ≤ 8 → m * newtonIter m j % 2 ^ (2 ^ j) = 1 % 2 ^ (2 ^ j)
  | 0, _ => by
      simp only [newtonIter, Nat.mul_one, pow_zero, pow_one]
      exact hodd
  | j + 1, hj => by
      have ih := newtonIter_spec hodd j (by omega)
      have hk : 2 * 2 ^ j ≤ 256 := by
        have : 2 ^ (j + 1) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) hj
        rw [pow_succ] at this
        omega
      have h := newton_step_nat hk ih (newtonStep_modEq m (newtonIter m j))
      rw [newtonIter_succ, pow_succ, Nat.mul_comm (2 ^ j) 2]
      exact h

/-- Eight Newton steps give the inverse of an odd `m` modulo `2^256`. -/
theorem newtonIter_eight {m : Nat} (hodd : m % 2 = 1) :
    m * newtonIter m 8 % Limbs.radix = 1 := by
  have h := newtonIter_spec hodd 8 le_rfl
  rw [show (2 : Nat) ^ 2 ^ 8 = Limbs.radix by rfl] at h
  rw [h]
  exact Nat.mod_eq_of_lt Limbs.radix_gt_one

/-- The negated inverse `-m⁻¹ mod 2^256` used by CIOS, computed from the
Newton inverse of the low limb. -/
theorem minv_spec {m x : Nat} (hx : m % Limbs.radix * x % Limbs.radix = 1) (hxr : x ≤ Limbs.radix) :
    (m * (Limbs.radix - x) + 1) % Limbs.radix = 0 :=
  minv_of_low_limb (negInv_spec Limbs.radix_gt_one hx hxr)

end Challenge.Modexp.Submission.Proofs.Fast.Model
