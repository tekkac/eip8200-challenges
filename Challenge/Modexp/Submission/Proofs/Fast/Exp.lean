import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P3
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P4
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P5
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P6
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Memory
import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Fast.Setup
import Challenge.Modexp.Submission.Proofs.Fast.Double
import Challenge.Modexp.Submission.Proofs.Fast.Ccb
import Challenge.Modexp.Submission.Proofs.Fast.R1
import Challenge.Modexp.Submission.Proofs.Fast.Lz
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P17
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# The three driver loops of the appended Montgomery path

After `Fast.Setup` has built `R1 = R mod m` and `CC = radix * R mod m` the
appended path runs three loops and returns:

1. **the `RR` chain** (idx 1155..1194, pc 1569..1638) — six iterations of
   square-and-multiply computing `RR = φ(radix ^ n) = R² mod m`;
2. **the base chain** (idx 1195..1264, pc 1639..1755) — a Horner loop over the
   base limbs producing `ACC = b mod m`, then `BASE = MonPro(ACC, RR)`;
3. **the exponent loop** (idx 1265..1332, pc 1756..1875) — `8 * esize`
   flagless square-and-multiply steps producing `ACC = φ(b ^ e)`, the final
   `MonPro(ACC, 1)` and the `RETURN`.

`MONPRO` (pc 1939) and `ADDMOD` (pc 2467) are developed in `Fast.Monpro` and
`Fast.Csub`; here they enter only through the abstract `Subroutines` contract,
so this module does not depend on those developments.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Exp

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

-- Lean 4.31 ships `List.getElem?_cons_zero` without the `simp` attribute, so the
-- program-counter tables of `Fast.Defs` (which end in `[…][i - lo]!`) do not
-- reduce inside the block-reduction `simp` calls without it.
attribute [local simp] List.getElem?_cons_zero

/-! ## Word-level helpers -/

theorem word_toNat_mul (a b : UInt256) :
    (a * b).toNat = a.toNat * b.toNat % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl

theorem ofNat_mul_mod (a b : Nat) :
    UInt256.ofNat a * UInt256.ofNat b = UInt256.ofNat (a * b) := by
  apply Challenge.EvmProof.Word.word_ext
  simp only [word_toNat_mul, Challenge.EvmProof.Word.word_toNat_ofNat, ← Nat.mul_mod]

theorem toNat_ofNat_self {a : Nat} (ha : a < 2 ^ 256) :
    (UInt256.ofNat a).toNat = a := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt ha]

theorem shr_ofNat (v k : Nat) (hv : v < 2 ^ 256) (hk : k < 256) :
    UInt256.shiftRight (UInt256.ofNat v) (UInt256.ofNat k) =
      UInt256.ofNat (v / 2 ^ k) := by
  rw [Challenge.EvmProof.Word.shiftRight_ofNat hv hk, Nat.shiftRight_eq_div_pow]

theorem and_one (v : Nat) : 1 &&& v = v % 2 := by
  rw [Nat.and_comm, Nat.and_one_is_mod]

theorem land_one (v : Nat) :
    UInt256.land (UInt256.ofNat 1) (UInt256.ofNat v) = UInt256.ofNat (v % 2) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (show (1 : Nat) < 2 ^ 256 by norm_num), and_one,
    Nat.mod_mod_of_dvd v (show (2 : Nat) ∣ 2 ^ 256 by exact ⟨2 ^ 255, by norm_num⟩),
    Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (Nat.mod_lt v (by norm_num)) (by norm_num))]

theorem land_ofNat (a b : Nat) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    UInt256.land (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a &&& b) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt (Nat.and_lt_two_pow a hb)]

theorem isZero_ofNat_zero : UInt256.isZero (UInt256.ofNat 0) = UInt256.ofNat 1 := by
  decide

theorem isZero_ofNat_of_ne {a : Nat} (ha : a < 2 ^ 256) (h : a ≠ 0) :
    UInt256.isZero (UInt256.ofNat a) = UInt256.ofNat 0 := by
  rw [UInt256.isZero, toNat_ofNat_self ha, if_neg h]

theorem isZero_ofNat_one : UInt256.isZero (UInt256.ofNat 1) = UInt256.ofNat 0 := by
  decide

theorem isTrue_one : UInt256.isTrue (UInt256.ofNat 1) := by decide

theorem not_isTrue_zero : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide

theorem isTrue_ofNat {a : Nat} (ha : a < 2 ^ 256) (h : a ≠ 0) :
    UInt256.isTrue (UInt256.ofNat a) := by
  show (UInt256.ofNat a).toNat ≠ 0
  rw [toNat_ofNat_self ha]
  exact h

/-! ## The stack frame and the subroutine contracts

The five outer words `[s32, n, bsize, esize, msize]` sit at the bottom of the
stack for the whole of the appended path; every state below carries them
explicitly. -/

/-- The persistent outer frame, top first. -/
def outer (n bsize esize msize : Nat) : List UInt256 :=
  [UInt256.ofNat (32 * n), UInt256.ofNat n, UInt256.ofNat bsize,
   UInt256.ofNat esize, UInt256.ofNat msize]

/-- The `MONPRO` call state, pc 1939, stack `[pa, pb, pd, ret] ++ tail`. -/
def mpCall (s : State) (mem : ByteArray) (pa pb pd : Nat) (ret : UInt256)
    (tail : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1939
           stack := UInt256.ofNat pa :: UInt256.ofNat pb :: UInt256.ofNat pd ::
             ret :: tail
           memory := mem }

/-- The `ADDMOD` call state, pc 2467, stack `[pa, pb, pd, ret] ++ tail`. -/
def amCall (s : State) (mem : ByteArray) (pa pb pd : Nat) (ret : UInt256)
    (tail : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2467
           stack := UInt256.ofNat pa :: UInt256.ofNat pb :: UInt256.ofNat pd ::
             ret :: tail
           memory := mem }

/-- The state a subroutine returns to. -/
def retTo (s : State) (mem : ByteArray) (ret : UInt256)
    (tail : List UInt256) : State :=
  { s with pc := ret, stack := tail, memory := mem }


/-! ### The configuration words

`V_S32 = 0x2480`, `V_MINV = 0x24A0`, `V_ML = 0x24C0`, `V_TL = 0x24E0` and
`V_EOFF = 0x2500` are written once by `Fast.Setup` and read by every
subroutine.  No transformer in the driver writes at or above `0x2480`, so the
whole bundle is preserved by a single lemma per transformer. -/
structure Frame (mem : ByteArray) (n bsize minv : Nat) : Prop where
  s32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n)
  minvW : MachineState.readWord mem 9376 = UInt256.ofNat minv
  ml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32)
  tl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n)
  eoff : MachineState.readWord mem 9472 = UInt256.ofNat (96 + bsize)

/-! ### The combined `ADDMOD` transformer

`Fast.Csub` splits the routine at pc 2680 into `gasSteps_addmod` (the schoolbook
add) and `gasSteps_csub` (the conditional subtract); the driver only ever calls
the pair.  `amMemOf` is the memory the pair leaves behind. -/

/-- The memory one `ADDMOD(pa, pb) → pd` call produces. -/
def amMemOf (mem : ByteArray) (pa pb n pd : Nat) : ByteArray :=
  Csub.csResultMemory (Csub.amResultMemory mem pa pb n) n pd

/-- One full `ADDMOD` call, `Csub.gasSteps_addmod` followed by
`Csub.gasSteps_csub`. -/
def gasSteps_addmodFull (s : State) (mem : ByteArray) (pa pb n pd : Nat)
    (ret : UInt256) (tail : List UInt256) (hcap : tail.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hpd : pd + 32 * n ≤ 8192)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n)) :
    Challenge.EvmProof.GasSteps (amCall s mem pa pb pd ret tail)
      (retTo s (amMemOf mem pa pb n pd) ret tail) :=
  have hpdN : (UInt256.ofNat pd).toNat = pd := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (show pd ≤ 8192 by omega) (by norm_num))]
  have hml' : MachineState.readWord (Csub.amResultMemory mem pa pb n) 9408 =
      UInt256.ofNat (32 * n - 32) := by
    rw [Double.readWord_amResultMemory_high _ pa pb n 9408 (by omega) hn32 (by omega)]
    exact hml
  have htl' : MachineState.readWord (Csub.amResultMemory mem pa pb n) 9440 =
      UInt256.ofNat (8224 + 32 * n) := by
    rw [Double.readWord_amResultMemory_high _ pa pb n 9440 (by omega) hn32 (by omega)]
    exact htl
  have hs32' : MachineState.readWord
      (Csub.csStep (Csub.amResultMemory mem pa pb n) n n).memory 9344 =
      UInt256.ofNat (32 * n) := by
    rw [Csub.csStep_readWord_disjoint _ n 9344 (by omega) (Or.inr (by omega)) n le_rfl,
      Double.readWord_amResultMemory_high _ pa pb n 9344 (by omega) hn32 (by omega)]
    exact hs32
  have htn : (MachineState.readWord
      (Csub.csStep (Csub.amResultMemory mem pa pb n) n n).memory 8224).toNat ≤ 1 := by
    rw [Csub.csStep_readWord_disjoint _ n 8224 (by omega) (Or.inr (by omega)) n le_rfl,
      Csub.addmod_tn]
    exact Csub.addmod_carry_le_one mem pa pb n hn (by omega) (by omega)
  have hdstFit : (UInt256.ofNat pd).toNat + 32 * n ≤ 9472 := by rw [hpdN]; omega
  Challenge.EvmProof.GasSteps.cast
    ((Csub.gasSteps_addmod s mem pa pb n (UInt256.ofNat pd) ret tail hcap hcode hfork
        hrun hnp hact hn hn32 hpa (by omega) hpb (by omega) hs32 htl).trans
      (Csub.gasSteps_csub s (Csub.amResultMemory mem pa pb n) n (UInt256.ofNat pd) ret
        tail hcap hcode hfork hrun hnp hact hn hn32 hjump hml' htl' hs32' hdstFit htn))
    rfl (by simp only [Csub.csReturnedState, retTo, amMemOf, Csub.csResultMemory, hpdN])

/-- `ADDMOD` writes only below `8256`, so nothing at or above `V_S32` moves. -/
theorem amMemOf_readWord_high (mem : ByteArray) (pa pb n pd addr : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (hpd : pd + 32 * n ≤ 8192) (haddr : 9344 ≤ addr) :
    MachineState.readWord (amMemOf mem pa pb n pd) addr =
      MachineState.readWord mem addr := by
  rw [amMemOf,
    Double.readWord_csResultMemory_high _ n pd addr hn hn32 (by omega) haddr,
    Double.readWord_amResultMemory_high _ pa pb n addr hn hn32 haddr]

/-- `ADDMOD` preserves the configuration words. -/
theorem amMemOf_frame {mem : ByteArray} {n bsize minv : Nat} (pa pb pd : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (hpd : pd + 32 * n ≤ 8192)
    (hf : Frame mem n bsize minv) : Frame (amMemOf mem pa pb n pd) n bsize minv := by
  have key : ∀ addr, 9344 ≤ addr →
      MachineState.readWord (amMemOf mem pa pb n pd) addr =
        MachineState.readWord mem addr :=
    fun addr haddr => amMemOf_readWord_high mem pa pb n pd addr hn hn32 hpd haddr
  exact ⟨by rw [key 9344 (by omega)]; exact hf.s32,
         by rw [key 9376 (by omega)]; exact hf.minvW,
         by rw [key 9408 (by omega)]; exact hf.ml,
         by rw [key 9440 (by omega)]; exact hf.tl,
         by rw [key 9472 (by omega)]; exact hf.eoff⟩

/-- `MONPRO` writes only below `9280`, so the configuration words survive. -/
theorem monproMem_frame' {s : State} {mem : ByteArray} {n bsize minv : Nat}
    (pa pb pd : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32) (hpd : pd + 32 * n ≤ 8192)
    (hf : Frame mem n bsize minv) :
    Frame (Monpro.monproMem s mem pa pb n pd) n bsize minv :=
  have key := Monpro.monproMem_frame s mem pa pb n pd hn hn32 hpd
  ⟨by rw [key.1]; exact hf.s32, by rw [key.2.1]; exact hf.minvW,
   by rw [key.2.2.1]; exact hf.ml, by rw [key.2.2.2.1]; exact hf.tl,
   by rw [key.2.2.2.2]; exact hf.eoff⟩

/-- The two subroutines this module calls, as abstract single-step contracts
carrying exactly the side conditions `Fast.Monpro.gasSteps_monproFull` and
`Fast.Csub.gasSteps_addmod`/`gasSteps_csub` require: the configuration words
(`Frame`), the pointer bounds, the return-address jump destination, and — for
`MONPRO` — the values of the two operand blocks. -/
structure Subroutines (s : State) (n bsize mm minv : Nat) where
  /-- The memory effect of `MonPro(pa, pb) → pd`. -/
  mpMem : Nat → Nat → Nat → ByteArray → ByteArray
  /-- The memory effect of `AddMod(pa, pb) → pd`. -/
  amMem : Nat → Nat → Nat → ByteArray → ByteArray
  /-- `MONPRO` preserves the configuration words. -/
  mpFrame : ∀ (pa pb pd : Nat) (mem : ByteArray), pd ≤ 6144 →
    Frame mem n bsize minv → Frame (mpMem pa pb pd mem) n bsize minv
  /-- `ADDMOD` preserves the configuration words. -/
  amFrame : ∀ (pa pb pd : Nat) (mem : ByteArray), pd ≤ 6144 →
    Frame mem n bsize minv → Frame (amMem pa pb pd mem) n bsize minv
  /-- `MONPRO` at pc 1939. -/
  monpro : ∀ (pa pb pd : Nat) (ret : UInt256) (tail : List UInt256)
    (mem : ByteArray) (a b : Nat), tail.length ≤ 1000 →
    32 ≤ pa → pa + 32 * n ≤ 8192 → 32 ≤ pb → pb + 32 * n ≤ 8192 →
    pd + 32 * n ≤ 8192 →
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true →
    Frame mem n bsize minv → Model.FastRepresents mem 0 n mm →
    Model.FastRepresents mem pa n a → Model.FastRepresents mem pb n b → a < mm →
    Challenge.EvmProof.GasSteps (mpCall s mem pa pb pd ret tail)
      (retTo s (mpMem pa pb pd mem) ret tail)
  /-- `ADDMOD` at pc 2467. -/
  addmod : ∀ (pa pb pd : Nat) (ret : UInt256) (tail : List UInt256)
    (mem : ByteArray), tail.length ≤ 1000 →
    32 ≤ pa → pa + 32 * n ≤ 8192 → 32 ≤ pb → pb + 32 * n ≤ 8192 →
    pd + 32 * n ≤ 8192 →
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true →
    Frame mem n bsize minv →
    Challenge.EvmProof.GasSteps (amCall s mem pa pb pd ret tail)
      (retTo s (amMem pa pb pd mem) ret tail)

/-! ## The `RR` chain

`RRL` (pc 1569) is entered with `[k] ++ OUTER` for `k = 5, 4, …, 0`; each
iteration squares `RR` and multiplies it by `R1` or `CC` according to bit `k`
of `n`.  The selected operand address is `R1 + 1024 * bit`, i.e. `0x1000` or
`0x1400`. -/

/-- Bit `k` of `v`. -/
def bitAt (v k : Nat) : Nat := v / 2 ^ k % 2

theorem bitAt_le_one (v k : Nat) : bitAt v k ≤ 1 := by
  unfold bitAt
  omega

/-- The branch-free operand selector: `R1` when bit `k` of `n` is clear, `CC`
when it is set. -/
def selOf (n k : Nat) : Nat := 4096 + 1024 * bitAt n k

/-- `RRL`, pc 1569, at the top of iteration `k`. -/
def rrHead (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  { s with pc := UInt256.ofNat 1569
           stack := UInt256.ofNat k :: outer n bsize esize msize
           memory := mem }

/-- pc 1586, back from the squaring `MonPro(RR, RR) → RR`. -/
def rrMid (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  { s with pc := UInt256.ofNat 1586
           stack := UInt256.ofNat k :: outer n bsize esize msize
           memory := mem }

/-- pc 2971, with the selector computed but the multiply not yet taken. -/
def rrSel (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  { s with pc := UInt256.ofNat 2971
           stack := UInt256.ofNat (selOf n k) :: UInt256.ofNat k ::
             outer n bsize esize msize
           memory := mem }

/-- pc 1615, back from the selected multiply, with the selector still live. -/
def rrPost (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  { s with pc := UInt256.ofNat 1615
           stack := UInt256.ofNat (selOf n k) :: UInt256.ofNat k ::
             outer n bsize esize msize
           memory := mem }

/-- pc 1623, the fallthrough that decrements the counter. -/
def rrNext (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  { s with pc := UInt256.ofNat 1623
           stack := UInt256.ofNat k :: outer n bsize esize msize
           memory := mem }

/-- `RRE`, pc 1631, reached once the counter has hit zero. -/
def rrDone (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 1631
           stack := UInt256.ofNat 0 :: outer n bsize esize msize
           memory := mem }

/-- pc 1639, the head of the base chain. -/
def baseHead (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 1639
           stack := outer n bsize esize msize
           memory := mem }

/-- `BDONE`, pc 1756, where the base chain rejoins. -/
def bDone (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 1756
           stack := outer n bsize esize msize
           memory := mem }

/-! ### Block reductions for the `RR` chain -/

set_option linter.unusedSimpArgs false in
/-- `blk1155` (pc 1569..1585): the loop head calls `MonPro(RR, RR) → RR`. -/
theorem run_rrHead (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1155
      (rrHead s mem n bsize esize msize k) =
      some (mpCall s mem 6144 6144 6144 (UInt256.ofNat 1586)
        (UInt256.ofNat k :: outer n bsize esize msize)) := by
  have h1939Nat : (UInt256.ofNat 1939).toNat = 1939 := by decide
  simp (config := { maxSteps := 400000 }) [blk1155, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rrHead, mpCall, outer, fastPC4, hcode, hrun, h1939Nat, jumpDest1939,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1162` (pc 1586..1614): pick `R1` or `CC` by bit `k` of `n` and call
`MonPro(RR, sel) → RR`. -/
theorem run_rrMid (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hn : n ≤ 32) (hk : k ≤ 5)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1162
      (rrMid s mem n bsize esize msize k) =
      some (rrSel s mem n bsize esize msize k) := by
  have hshr : UInt256.shiftRight (UInt256.ofNat n) (UInt256.ofNat k) =
      UInt256.ofNat (n / 2 ^ k) :=
    shr_ofNat n k (Nat.lt_of_le_of_lt hn (by norm_num)) (by omega)
  have hand : UInt256.land (UInt256.ofNat 1) (UInt256.ofNat (n / 2 ^ k)) =
      UInt256.ofNat (n / 2 ^ k % 2) := land_one _
  simp (config := { maxSteps := 600000 }) [blk1162, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rrMid, rrSel, outer, selOf, bitAt, fastPC4, fastPC5, hcode, hrun,
    hshr, hand, ofNat_mul_mod, jumpDest2971,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

/-- pc 2981, the multiply's call frame about to be pushed. -/
def rrCallSel (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  { s with pc := UInt256.ofNat 2981
           stack := UInt256.ofNat (selOf n k) :: UInt256.ofNat k ::
             outer n bsize esize msize
           memory := mem }

/-- pc 2995, the skip. -/
def rrSkipSel (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  { s with pc := UInt256.ofNat 2995
           stack := UInt256.ofNat (selOf n k) :: UInt256.ofNat k ::
             outer n bsize esize msize
           memory := mem }

set_option linter.unusedSimpArgs false in
/-- `blk1816` with bit `k` of `n` set: the selector is `CC`, take the multiply. -/
theorem run_rrSel_call (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hbit : bitAt n k ≠ 0)
    (_hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1816
      (rrSel s mem n bsize esize msize k) =
      some (rrCallSel s mem n bsize esize msize k) := by
  have h1 : bitAt n k = 1 := by have := bitAt_le_one n k; omega
  have hsel : selOf n k = 5120 := by unfold selOf; rw [h1]
  have heq : UInt256.eq (UInt256.ofNat 4096) (UInt256.ofNat 5120) = UInt256.ofNat 0 := by
    decide
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  simp (config := { maxSteps := 400000 }) [blk1816, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rrSel, rrCallSel, outer, hsel, heq, hfalse, hrun, fastPC23,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1816` with bit `k` clear: the selector is `R1`, skip the multiply. -/
theorem run_rrSel_skip (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hbit : bitAt n k = 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1816
      (rrSel s mem n bsize esize msize k) =
      some (rrSkipSel s mem n bsize esize msize k) := by
  have hsel : selOf n k = 4096 := by unfold selOf; rw [hbit]
  have heq : UInt256.eq (UInt256.ofNat 4096) (UInt256.ofNat 4096) = UInt256.ofNat 1 := by
    decide
  have htrue : UInt256.isTrue (UInt256.ofNat 1) := by decide
  simp (config := { maxSteps := 400000 }) [blk1816, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rrSel, rrSkipSel, outer, hsel, heq, htrue, hcode, hrun, fastPC23, jumpDest2995,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1822`: the multiply's call frame. -/
theorem run_rrCallSel (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1822
      (rrCallSel s mem n bsize esize msize k) =
      some (mpCall s mem 6144 (selOf n k) 6144 (UInt256.ofNat 1615)
        (UInt256.ofNat (selOf n k) :: UInt256.ofNat k ::
          outer n bsize esize msize)) := by
  simp (config := { maxSteps := 400000 }) [blk1822, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rrCallSel, mpCall, outer, hcode, hrun, fastPC23, jumpDest1939,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1828`: the skip rejoins the round at pc 1615. -/
theorem run_rrSkipSel (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1828
      (rrSkipSel s mem n bsize esize msize k) =
      some (rrPost s mem n bsize esize msize k) := by
  simp (config := { maxSteps := 400000 }) [blk1828, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rrSkipSel, rrPost, outer, hcode, hrun, fastPC23, jumpDest1615,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_rrPost_loop (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) (hk : k ≤ 5) (hk0 : k ≠ 0)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1178
      (rrPost s mem n bsize esize msize k) =
      some (rrNext s mem n bsize esize msize k) := by
  have hzero : UInt256.isZero (UInt256.ofNat k) = UInt256.ofNat 0 :=
    isZero_ofNat_of_ne (Nat.lt_of_le_of_lt hk (by norm_num)) hk0
  simp (config := { maxSteps := 400000 }) [blk1178, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rrPost, rrNext, outer, hrun, hzero,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1178` (pc 1615..1622) with the counter at zero: leave the chain. -/
theorem run_rrPost_exit (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1178
      (rrPost s mem n bsize esize msize 0) =
      some (rrDone s mem n bsize esize msize) := by
  have h1631Nat : (UInt256.ofNat 1631).toNat = 1631 := by decide
  simp (config := { maxSteps := 400000 }) [blk1178, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rrPost, rrDone, outer, hcode, hrun, isZero_ofNat_zero, isTrue_one,
    h1631Nat, jumpDest1631,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1184` (pc 1623..1630): decrement the counter and loop. -/
theorem run_rrNext (s : State) (mem : ByteArray)
    (n bsize esize msize k k' : Nat) (hk : k = k' + 1) (hk5 : k ≤ 5)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1184
      (rrNext s mem n bsize esize msize k) =
      some (rrHead s mem n bsize esize msize k') := by
  subst hk
  have hsub : UInt256.ofNat (k' + 1) - UInt256.ofNat 1 = UInt256.ofNat k' := by
    have h := Challenge.EvmProof.Word.ofNat_sub_ofNat
      (a := k' + 1) (b := 1) (by omega) (Nat.lt_of_le_of_lt hk5 (by norm_num))
    rwa [Nat.add_sub_cancel] at h
  have h1569Nat : (UInt256.ofNat 1569).toNat = 1569 := by decide
  simp (config := { maxSteps := 400000 }) [blk1184, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rrNext, rrHead, outer, hcode, hrun, hsub, h1569Nat, jumpDest1569,
    List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1189` (pc 1631..1638) with a nonempty base: enter the base chain. -/
theorem run_rrDone_base (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hb : bsize ≤ 1024) (hb0 : bsize ≠ 0) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1189
      (rrDone s mem n bsize esize msize) =
      some (baseHead s mem n bsize esize msize) := by
  have hzero : UInt256.isZero (UInt256.ofNat bsize) = UInt256.ofNat 0 :=
    isZero_ofNat_of_ne (Nat.lt_of_le_of_lt hb (by norm_num)) hb0
  simp (config := { maxSteps := 400000 }) [blk1189, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rrDone, baseHead, outer, hrun, hzero, not_isTrue_zero,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1189` (pc 1631..1638) with an empty base: skip the base chain. -/
theorem run_rrDone_skip (s : State) (mem : ByteArray) (n esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1189
      (rrDone s mem n 0 esize msize) =
      some (bDone s mem n 0 esize msize) := by
  have h1756Nat : (UInt256.ofNat 1756).toNat = 1756 := by decide
  simp (config := { maxSteps := 400000 }) [blk1189, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rrDone, bDone, outer, hcode, hrun, isZero_ofNat_zero, isTrue_one,
    h1756Nat, jumpDest1756,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]


/-! ### The `RR` loop -/

@[simp] theorem outer_length (n bsize esize msize : Nat) :
    (outer n bsize esize msize).length = 5 := by
  simp [outer]

def gasSteps_rrHead (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (rrHead s mem n bsize esize msize k)
      (mpCall s mem 6144 6144 6144 (UInt256.ofNat 1586)
        (UInt256.ofNat k :: outer n bsize esize msize)) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1155 hcode hfork
      (run_rrHead s mem n bsize esize msize k hcode hrun) hrun hnp

def gasSteps_rrMid (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hn : n ≤ 32) (hk : k ≤ 5)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (rrMid s mem n bsize esize msize k)
      (rrSel s mem n bsize esize msize k) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1162 hcode hfork
      (run_rrMid s mem n bsize esize msize k hn hk hcode hrun) hrun hnp

def gasSteps_rrSelCall (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hbit : bitAt n k ≠ 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (rrSel s mem n bsize esize msize k)
      (rrCallSel s mem n bsize esize msize k) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1816 hcode hfork
      (run_rrSel_call s mem n bsize esize msize k hbit hcode hrun) hrun hnp

def gasSteps_rrSelSkip (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hbit : bitAt n k = 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (rrSel s mem n bsize esize msize k)
      (rrSkipSel s mem n bsize esize msize k) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1816 hcode hfork
      (run_rrSel_skip s mem n bsize esize msize k hbit hcode hrun) hrun hnp

def gasSteps_rrCallSel (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (rrCallSel s mem n bsize esize msize k)
      (mpCall s mem 6144 (selOf n k) 6144 (UInt256.ofNat 1615)
        (UInt256.ofNat (selOf n k) :: UInt256.ofNat k ::
          outer n bsize esize msize)) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1822 hcode hfork
      (run_rrCallSel s mem n bsize esize msize k hcode hrun) hrun hnp

def gasSteps_rrSkipSel (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (rrSkipSel s mem n bsize esize msize k)
      (rrPost s mem n bsize esize msize k) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1828 hcode hfork
      (run_rrSkipSel s mem n bsize esize msize k hcode hrun) hrun hnp

def gasSteps_rrPost_loop (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) (hk : k ≤ 5) (hk0 : k ≠ 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (rrPost s mem n bsize esize msize k)
      (rrNext s mem n bsize esize msize k) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1178 hcode hfork
      (run_rrPost_loop s mem n bsize esize msize k hk hk0 hrun) hrun hnp

def gasSteps_rrPost_exit (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (rrPost s mem n bsize esize msize 0)
      (rrDone s mem n bsize esize msize) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1178 hcode hfork
      (run_rrPost_exit s mem n bsize esize msize hcode hrun) hrun hnp

def gasSteps_rrNext (s : State) (mem : ByteArray) (n bsize esize msize k k' : Nat)
    (hk : k = k' + 1) (hk5 : k ≤ 5)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (rrNext s mem n bsize esize msize k)
      (rrHead s mem n bsize esize msize k') :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1184 hcode hfork
      (run_rrNext s mem n bsize esize msize k k' hk hk5 hcode hrun) hrun hnp

def gasSteps_rrDone_base (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hb : bsize ≤ 1024) (hb0 : bsize ≠ 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (rrDone s mem n bsize esize msize)
      (baseHead s mem n bsize esize msize) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1189 hcode hfork
      (run_rrDone_base s mem n bsize esize msize hb hb0 hrun) hrun hnp

def gasSteps_rrDone_skip (s : State) (mem : ByteArray) (n esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (rrDone s mem n 0 esize msize)
      (bDone s mem n 0 esize msize) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1189 hcode hfork
      (run_rrDone_skip s mem n esize msize hcode hrun) hrun hnp

/-- One `RR` round: square, and multiply by `CC` only when bit `k` of `n` is
set.  When it is clear the selector would be `R1`, the Montgomery form of one,
so the multiply is the identity and the block skips the call. -/
def rrStep (mpMem : Nat → Nat → Nat → ByteArray → ByteArray) (n k : Nat)
    (mem : ByteArray) : ByteArray :=
  if bitAt n k = 0 then mpMem 6144 6144 6144 mem
  else mpMem 6144 5120 6144 (mpMem 6144 6144 6144 mem)

/-- The memory after `i` iterations of the `RR` chain. -/
def rrMem (mpMem : Nat → Nat → Nat → ByteArray → ByteArray) (n : Nat)
    (mem : ByteArray) : Nat → ByteArray
  | 0 => mem
  | i + 1 => rrStep mpMem n (5 - i) (rrMem mpMem n mem i)

/-- The indexed loop-head family of the `RR` chain. -/
def rrFamily (s : State) (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (mem : ByteArray) (n bsize esize msize i : Nat) : State :=
  rrHead s (rrMem mpMem n mem i) n bsize esize msize (5 - i)












/-! ## The base chain

`BL` (pc 1668) walks `j` from `1` to `pb = ⌈bsize / 32⌉`, alternating
`MonPro(ACC, CC) → ACC` and `AddMod(ACC, ONE) → ACC`; the most significant
partial limb of the base is stored before the loop and limb `pb - 1 - j` is
stored into `ONE` inside iteration `j`. -/

theorem lt_ofNat_of_lt {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : a < b) :
    UInt256.lt (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat 1 := by
  rw [UInt256.lt, toNat_ofNat_self ha, toNat_ofNat_self hb, if_pos h]

theorem lt_ofNat_of_le {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : b ≤ a) :
    UInt256.lt (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat 0 := by
  rw [UInt256.lt, toNat_ofNat_self ha, toNat_ofNat_self hb,
    if_neg (Nat.not_lt.mpr h)]

/-- The number of limbs of the base. -/
def pbOf (bsize : Nat) : Nat := (31 + bsize) / 32

/-- The width in bytes of the most significant (partial) base limb. -/
def topWidth (bsize : Nat) : Nat := bsize - 32 * (pbOf bsize - 1)

/-- `BL`, pc 1668, with the base-limb counter at `j`. -/
def blHead (s : State) (mem : ByteArray) (n bsize esize msize pb j : Nat) : State :=
  { s with pc := UInt256.ofNat 1668
           stack := UInt256.ofNat j :: UInt256.ofNat pb :: outer n bsize esize msize
           memory := mem }

/-- pc 1677, the loop body which calls `MonPro(ACC, CC) → ACC`. -/
def blMul (s : State) (mem : ByteArray) (n bsize esize msize pb j : Nat) : State :=
  { s with pc := UInt256.ofNat 1677
           stack := UInt256.ofNat j :: UInt256.ofNat pb :: outer n bsize esize msize
           memory := mem }

/-- pc 1693, back from the multiply. -/
def blAdd (s : State) (mem : ByteArray) (n bsize esize msize pb j : Nat) : State :=
  { s with pc := UInt256.ofNat 1693
           stack := UInt256.ofNat j :: UInt256.ofNat pb :: outer n bsize esize msize
           memory := mem }

/-- pc 1728, back from the add. -/
def blNext (s : State) (mem : ByteArray) (n bsize esize msize pb j : Nat) : State :=
  { s with pc := UInt256.ofNat 1728
           stack := UInt256.ofNat j :: UInt256.ofNat pb :: outer n bsize esize msize
           memory := mem }

/-- `BLE`, pc 1736, where the Horner loop ends. -/
def blExit (s : State) (mem : ByteArray) (n bsize esize msize pb j : Nat) : State :=
  { s with pc := UInt256.ofNat 1736
           stack := UInt256.ofNat j :: UInt256.ofNat pb :: outer n bsize esize msize
           memory := mem }

/-- pc 1755, back from `BASE := MonPro(ACC, RR)`. -/
def bRejoin (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 1755
           stack := outer n bsize esize msize
           memory := mem }

set_option linter.unusedSimpArgs false in
/-- `blk1216` (pc 1668..1676) with `j < pb`: run the body. -/
theorem run_blHead_body (s : State) (mem : ByteArray)
    (n bsize esize msize pb j : Nat) (hpb : pb ≤ 32) (hj : j < pb)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1216
      (blHead s mem n bsize esize msize pb j) =
      some (blMul s mem n bsize esize msize pb j) := by
  have hlt : UInt256.lt (UInt256.ofNat j) (UInt256.ofNat pb) = UInt256.ofNat 1 :=
    lt_ofNat_of_lt (Nat.lt_of_lt_of_le hj (Nat.le_trans hpb (by norm_num)))
      (Nat.lt_of_le_of_lt hpb (by norm_num)) hj
  simp (config := { maxSteps := 400000 }) [blk1216, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    blHead, blMul, outer, hrun, hlt, isZero_ofNat_one, not_isTrue_zero,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1216` (pc 1668..1676) with `pb ≤ j`: leave the loop. -/
theorem run_blHead_exit (s : State) (mem : ByteArray)
    (n bsize esize msize pb j : Nat) (hpb : pb ≤ 32) (hj : j ≤ 32) (hje : pb ≤ j)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1216
      (blHead s mem n bsize esize msize pb j) =
      some (blExit s mem n bsize esize msize pb j) := by
  have hlt : UInt256.lt (UInt256.ofNat j) (UInt256.ofNat pb) = UInt256.ofNat 0 :=
    lt_ofNat_of_le (Nat.lt_of_le_of_lt hj (by norm_num))
      (Nat.lt_of_le_of_lt hpb (by norm_num)) hje
  have h1736Nat : (UInt256.ofNat 1736).toNat = 1736 := by decide
  simp (config := { maxSteps := 400000 }) [blk1216, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    blHead, blExit, outer, hcode, hrun, hlt, isZero_ofNat_zero, isTrue_one,
    h1736Nat, jumpDest1736,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1223` (pc 1677..1692): call `MonPro(ACC, CC) → ACC`. -/
theorem run_blMul (s : State) (mem : ByteArray) (n bsize esize msize pb j : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1223
      (blMul s mem n bsize esize msize pb j) =
      some (mpCall s mem 1024 5120 1024 (UInt256.ofNat 1693)
        (UInt256.ofNat j :: UInt256.ofNat pb :: outer n bsize esize msize)) := by
  have h1939Nat : (UInt256.ofNat 1939).toNat = 1939 := by decide
  simp (config := { maxSteps := 400000 }) [blk1223, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    blMul, mpCall, outer, hcode, hrun, h1939Nat, jumpDest1939,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1250` (pc 1728..1735): bump the counter and loop. -/
theorem run_blNext (s : State) (mem : ByteArray) (n bsize esize msize pb j : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1250
      (blNext s mem n bsize esize msize pb j) =
      some (blHead s mem n bsize esize msize pb (j + 1)) := by
  have hcomm : 1 + j = j + 1 := Nat.add_comm 1 j
  have h1668Nat : (UInt256.ofNat 1668).toNat = 1668 := by decide
  simp (config := { maxSteps := 400000 }) [blk1250, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    blNext, blHead, outer, hcode, hrun, hcomm, h1668Nat, jumpDest1668,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1255` (pc 1736..1754): drop the loop variables and call
`MonPro(ACC, RR) → BASE`. -/
theorem run_blExit (s : State) (mem : ByteArray) (n bsize esize msize pb j : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1255
      (blExit s mem n bsize esize msize pb j) =
      some (mpCall s mem 1024 6144 2048 (UInt256.ofNat 1755)
        (outer n bsize esize msize)) := by
  have h1939Nat : (UInt256.ofNat 1939).toNat = 1939 := by decide
  simp (config := { maxSteps := 400000 }) [blk1255, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    blExit, mpCall, outer, hcode, hrun, h1939Nat, jumpDest1939,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1264` (pc 1755): the one-instruction rejoin. -/
theorem run_bRejoin (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1264
      (bRejoin s mem n bsize esize msize) =
      some (bDone s mem n bsize esize msize) := by
  simp (config := { maxSteps := 200000 }) [blk1264, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    bRejoin, bDone, outer, hrun,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]


/-! ### Memory writes and the active-word high-water mark

Every address the appended path touches lies below `0x2540`, so once the setup
block has stored `V_N` at `0x2520` no access here moves the high-water mark. -/

theorem mod_word_self {a : Nat} (h : a < 2 ^ 256) :
    a % 115792089237316195423570985008687907853269984665640564039457584007913129639936
      = a :=
  Nat.mod_eq_of_lt h

theorem push0_word : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide

/-- One 32-byte store. -/
def storeWord (mem : ByteArray) (addr : Nat) (w : UInt256) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded w.toNat 32) addr

/-- One `MCOPY`. -/
def mcopyMem (mem : ByteArray) (dst src sz : Nat) : ByteArray :=
  MachineState.writeBytes mem (MachineState.readPadded mem src sz) dst

theorem activeWordsAfter_fix (curr off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 9536) (hcurr : 298 ≤ curr) :
    MachineState.activeWordsAfter curr off sz = curr := by
  unfold MachineState.activeWordsAfter
  simp only [hsz, if_false]
  have hle : (off + sz - 1) / 32 + 1 ≤ curr := by omega
  exact Nat.max_eq_left hle

theorem activeWords_fix (s : State) (off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 9536) (hact : 298 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat off sz) =
      s.activeWords := by
  rw [activeWordsAfter_fix _ off sz hsz hoff hact]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm

theorem activeWords_fix2 (s : State) (off1 sz1 off2 sz2 : Nat)
    (hsz1 : sz1 ≠ 0) (hsz2 : sz2 ≠ 0)
    (hoff1 : off1 + sz1 ≤ 9536) (hoff2 : off2 + sz2 ≤ 9536)
    (hact : 298 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter
      (MachineState.activeWordsAfter s.activeWords.toNat off1 sz1) off2 sz2) =
      s.activeWords := by
  rw [activeWordsAfter_fix _ off1 sz1 hsz1 hoff1 hact,
    activeWordsAfter_fix _ off2 sz2 hsz2 hoff2 hact]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm

/-! ### The head of the base chain and the loop body -/

/-- The most significant, possibly partial, limb of the base. -/
def topLimbOf (input : ByteArray) (bsize : Nat) : Nat :=
  Precompile.bytesToNatPadded input 96 (topWidth bsize)

/-- The base limb iteration `j` stores into `ONE`: limb `pb - 1 - j` counted
from the least significant. -/
def baseLimbWord (input : ByteArray) (bsize pb j : Nat) : UInt256 :=
  MachineState.readWord input (96 + (bsize - 32 * (pb - j)))

set_option linter.unusedSimpArgs false in
/-- `blk1195` (pc 1639..1666): compute the limb count, store the top partial
limb into `ACC` and start the Horner loop at `j = 1`. -/
theorem run_baseHead (s : State) (mem input : ByteArray) (n bsize esize msize : Nat)
    (hdata : s.executionEnv.calldata = input)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hb : bsize ≤ 1024) (hb0 : 1 ≤ bsize)
    (hact : 298 ≤ s.activeWords.toNat) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1195
      (baseHead s mem n bsize esize msize) =
      some (blHead s (storeWord mem (992 + 32 * n)
        (UInt256.ofNat (topLimbOf input bsize))) n bsize esize msize
        (pbOf bsize) 1) := by
  have hpb1 : 1 ≤ pbOf bsize := by unfold pbOf; omega
  have hpbLe : pbOf bsize ≤ 32 := by unfold pbOf; omega
  have hpbBig : bsize ≤ 32 * pbOf bsize := by unfold pbOf; omega
  have hpbLow : 32 * (pbOf bsize - 1) < bsize := by unfold pbOf; omega
  have htw1 : 0 < topWidth bsize := by unfold topWidth; omega
  have htw32 : topWidth bsize ≤ 32 := by unfold topWidth; omega
  have hshiftEq : 32 * pbOf bsize - bsize = 32 - topWidth bsize := by
    unfold topWidth; omega
  have hshr : UInt256.shiftRight (UInt256.ofNat (31 + bsize)) (UInt256.ofNat 5) =
      UInt256.ofNat ((31 + bsize) / 2 ^ 5) :=
    shr_ofNat _ 5 (Nat.lt_of_le_of_lt (show 31 + bsize ≤ 1055 by omega) (by norm_num))
      (by omega)
  have hpb : (31 + bsize) / 32 = pbOf bsize := rfl
  have hshl : UInt256.shiftLeft (UInt256.ofNat (pbOf bsize)) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * pbOf bsize) := by
    have he : pbOf bsize * 2 ^ 5 = 32 * pbOf bsize := by ring
    have h1 : pbOf bsize < 2 ^ 256 := Nat.lt_of_le_of_lt hpbLe (by norm_num)
    have h2 : (5 : Nat) < 256 := by omega
    have h3 : pbOf bsize * 2 ^ 5 < 2 ^ 256 := by
      rw [he]
      exact Nat.lt_of_le_of_lt (show 32 * pbOf bsize ≤ 1024 by omega) (by norm_num)
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat h1 h2 h3]
    exact congrArg UInt256.ofNat he
  have hsub : UInt256.ofNat (32 * pbOf bsize) - UInt256.ofNat bsize =
      UInt256.ofNat (32 * pbOf bsize - bsize) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat hpbBig
      (Nat.lt_of_le_of_lt (show 32 * pbOf bsize ≤ 1024 by omega) (by norm_num))
  have hshl2 : UInt256.shiftLeft (UInt256.ofNat (32 * pbOf bsize - bsize))
      (UInt256.ofNat 3) = UInt256.ofNat ((32 - topWidth bsize) * 8) := by
    have he : (32 * pbOf bsize - bsize) * 2 ^ 3 = (32 - topWidth bsize) * 8 := by
      rw [← hshiftEq]; ring
    have h1 : 32 * pbOf bsize - bsize < 2 ^ 256 :=
      Nat.lt_of_le_of_lt (show 32 * pbOf bsize - bsize ≤ 1024 by omega) (by norm_num)
    have h2 : (3 : Nat) < 256 := by omega
    have h3 : (32 * pbOf bsize - bsize) * 2 ^ 3 < 2 ^ 256 := by
      rw [he]
      exact Nat.lt_of_le_of_lt (show (32 - topWidth bsize) * 8 ≤ 256 by omega)
        (by norm_num)
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat h1 h2 h3]
    exact congrArg UInt256.ofNat he
  have hsr : UInt256.shiftRight (MachineState.readWord input 96)
      (UInt256.ofNat ((32 - topWidth bsize) * 8)) =
      UInt256.ofNat (topLimbOf input bsize) :=
    Challenge.EvmProof.Bytes.shiftRight_readWord input 96 (topWidth bsize) htw1 htw32
  have hmod : (992 + 32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 992 + 32 * n := mod_word_self (by
        exact Nat.lt_of_le_of_lt (show 992 + 32 * n ≤ 2016 by omega) (by norm_num))
  have hfix : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (992 + 32 * n) 32) = s.activeWords :=
    activeWords_fix s (992 + 32 * n) 32 (by omega) (by omega) hact
  simp (config := { maxSteps := 800000 }) [blk1195, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    baseHead, blHead, storeWord, outer, hdata, hrun, hshr, hpb, hshl, hsub,
    hshl2, hsr, hmod, hfix, List.exchange, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1229` (pc 1693..1727): store base limb `pb - 1 - j` into `ONE` and call
`AddMod(ACC, ONE) → ACC`. -/
theorem run_blAdd (s : State) (mem input : ByteArray)
    (n bsize esize msize pb j : Nat)
    (hdata : s.executionEnv.calldata = input)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hb : bsize ≤ 1024) (hpb : pb ≤ 32) (_hj : 1 ≤ j)
    (hjpb : j ≤ pb) (hle : 32 * (pb - j) ≤ bsize)
    (hact : 298 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1229
      (blAdd s mem n bsize esize msize pb j) =
      some (amCall s (storeWord mem (3040 + 32 * n) (baseLimbWord input bsize pb j))
        1024 3072 1024 (UInt256.ofNat 1728)
        (UInt256.ofNat j :: UInt256.ofNat pb :: outer n bsize esize msize)) := by
  have hsub1 : UInt256.ofNat pb - UInt256.ofNat j = UInt256.ofNat (pb - j) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat hjpb
      (Nat.lt_of_le_of_lt hpb (by norm_num))
  have hshl : UInt256.shiftLeft (UInt256.ofNat (pb - j)) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * (pb - j)) := by
    have he : (pb - j) * 2 ^ 5 = 32 * (pb - j) := by ring
    have h1 : pb - j < 2 ^ 256 :=
      Nat.lt_of_le_of_lt (show pb - j ≤ 32 by omega) (by norm_num)
    have h2 : (5 : Nat) < 256 := by omega
    have h3 : (pb - j) * 2 ^ 5 < 2 ^ 256 := by
      rw [he]
      exact Nat.lt_of_le_of_lt (show 32 * (pb - j) ≤ 1024 by omega) (by norm_num)
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat h1 h2 h3]
    exact congrArg UInt256.ofNat he
  have hsub2 : UInt256.ofNat bsize - UInt256.ofNat (32 * (pb - j)) =
      UInt256.ofNat (bsize - 32 * (pb - j)) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat hle
      (Nat.lt_of_le_of_lt hb (by norm_num))
  have hmodOff : (96 + (bsize - 32 * (pb - j))) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 96 + (bsize - 32 * (pb - j)) :=
    mod_word_self (Nat.lt_of_le_of_lt
      (show 96 + (bsize - 32 * (pb - j)) ≤ 1120 by omega) (by norm_num))
  have hmod : (3040 + 32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 3040 + 32 * n :=
    mod_word_self (Nat.lt_of_le_of_lt (show 3040 + 32 * n ≤ 4064 by omega) (by norm_num))
  have hfix : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (3040 + 32 * n) 32) = s.activeWords :=
    activeWords_fix s (3040 + 32 * n) 32 (by omega) (by omega) hact
  have h2467Nat : (UInt256.ofNat 2467).toNat = 2467 := by decide
  simp (config := { maxSteps := 800000 }) [blk1229, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    blAdd, amCall, storeWord, baseLimbWord, outer, hdata, hcode, hrun, hsub1, hshl,
    hsub2, hmodOff, hmod, hfix, h2467Nat, jumpDest2467,
    State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]


/-! ### The base loop -/

def gasSteps_baseHead (s : State) (mem input : ByteArray) (n bsize esize msize : Nat)
    (hdata : s.executionEnv.calldata = input)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hb : bsize ≤ 1024) (hb0 : 1 ≤ bsize)
    (hact : 298 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (baseHead s mem n bsize esize msize)
      (blHead s (storeWord mem (992 + 32 * n)
        (UInt256.ofNat (topLimbOf input bsize))) n bsize esize msize
        (pbOf bsize) 1) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1195 hcode hfork
      (run_baseHead s mem input n bsize esize msize hdata hn hn32 hb hb0 hact hrun)
      hrun hnp

def gasSteps_blBodyHead (s : State) (mem : ByteArray)
    (n bsize esize msize pb j : Nat) (hpb : pb ≤ 32) (hj : j < pb)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (blHead s mem n bsize esize msize pb j)
      (blMul s mem n bsize esize msize pb j) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1216 hcode hfork
      (run_blHead_body s mem n bsize esize msize pb j hpb hj hrun) hrun hnp

def gasSteps_blHeadExit (s : State) (mem : ByteArray)
    (n bsize esize msize pb j : Nat) (hpb : pb ≤ 32) (hj : j ≤ 32) (hje : pb ≤ j)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (blHead s mem n bsize esize msize pb j)
      (blExit s mem n bsize esize msize pb j) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1216 hcode hfork
      (run_blHead_exit s mem n bsize esize msize pb j hpb hj hje hcode hrun) hrun hnp

def gasSteps_blMul (s : State) (mem : ByteArray) (n bsize esize msize pb j : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (blMul s mem n bsize esize msize pb j)
      (mpCall s mem 1024 5120 1024 (UInt256.ofNat 1693)
        (UInt256.ofNat j :: UInt256.ofNat pb :: outer n bsize esize msize)) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1223 hcode hfork
      (run_blMul s mem n bsize esize msize pb j hcode hrun) hrun hnp

def gasSteps_blAdd (s : State) (mem input : ByteArray)
    (n bsize esize msize pb j : Nat)
    (hdata : s.executionEnv.calldata = input)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hb : bsize ≤ 1024) (hpb : pb ≤ 32) (hj : 1 ≤ j)
    (hjpb : j ≤ pb) (hle : 32 * (pb - j) ≤ bsize)
    (hact : 298 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (blAdd s mem n bsize esize msize pb j)
      (amCall s (storeWord mem (3040 + 32 * n) (baseLimbWord input bsize pb j))
        1024 3072 1024 (UInt256.ofNat 1728)
        (UInt256.ofNat j :: UInt256.ofNat pb :: outer n bsize esize msize)) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1229 hcode hfork
      (run_blAdd s mem input n bsize esize msize pb j hdata hn hn32 hb hpb hj hjpb
        hle hact hcode hrun) hrun hnp

def gasSteps_blNext (s : State) (mem : ByteArray) (n bsize esize msize pb j : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (blNext s mem n bsize esize msize pb j)
      (blHead s mem n bsize esize msize pb (j + 1)) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1250 hcode hfork
      (run_blNext s mem n bsize esize msize pb j hcode hrun) hrun hnp

def gasSteps_blExit (s : State) (mem : ByteArray) (n bsize esize msize pb j : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (blExit s mem n bsize esize msize pb j)
      (mpCall s mem 1024 6144 2048 (UInt256.ofNat 1755)
        (outer n bsize esize msize)) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1255 hcode hfork
      (run_blExit s mem n bsize esize msize pb j hcode hrun) hrun hnp

def gasSteps_bRejoin (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (bRejoin s mem n bsize esize msize)
      (bDone s mem n bsize esize msize) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1264 hcode hfork
      (run_bRejoin s mem n bsize esize msize hrun) hrun hnp

/-- The memory after `t` iterations of the Horner loop. -/
def blMems (mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (input : ByteArray) (n bsize pb : Nat) (mem : ByteArray) : Nat → ByteArray
  | 0 => mem
  | t + 1 =>
      amMem 1024 3072 1024
        (storeWord (mpMem 1024 5120 1024 (blMems mpMem amMem input n bsize pb mem t))
          (3040 + 32 * n) (baseLimbWord input bsize pb (t + 1)))

/-- The indexed loop-head family of the Horner loop. -/
def blFamily (s : State) (mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (input mem : ByteArray) (n bsize esize msize pb t : Nat) : State :=
  blHead s (blMems mpMem amMem input n bsize pb mem t) n bsize esize msize pb (t + 1)



/-! ## The exponent loop

`EB` (pc 1769) walks the `esize` exponent bytes; for each byte `EBIT`
(pc 1789) walks its eight bits from the most significant, squaring `ACC` on
every bit and multiplying by `BASE` on set bits. -/

/-- Exponent byte `i`, counted from the most significant. -/
def expByte (input : ByteArray) (bsize i : Nat) : Nat :=
  (YulSemantics.EVM.byteFrom input.toList (96 + bsize + i)).toNat

/-- `EB`, pc 1769, at the top of exponent byte `i`. -/
def ebHead (s : State) (mem : ByteArray) (n bsize esize msize i : Nat) : State :=
  { s with pc := UInt256.ofNat 1769
           stack := UInt256.ofNat i :: outer n bsize esize msize
           memory := mem }

/-- pc 1778, which loads exponent byte `i`. -/
def ebLoad (s : State) (mem : ByteArray) (n bsize esize msize i : Nat) : State :=
  { s with pc := UInt256.ofNat 1778
           stack := UInt256.ofNat i :: outer n bsize esize msize
           memory := mem }

/-- The live bit-loop stack. -/
def bitStack (n bsize esize msize i w mask : Nat) : List UInt256 :=
  UInt256.ofNat mask :: UInt256.ofNat w :: UInt256.ofNat i ::
    outer n bsize esize msize

/-- `EBIT`, pc 1789. -/
def ebitHead (s : State) (mem : ByteArray) (n bsize esize msize i w mask : Nat) :
    State :=
  { s with pc := UInt256.ofNat 1789
           stack := bitStack n bsize esize msize i w mask
           memory := mem }

/-- pc 1806, back from the squaring. -/
def ebitTest (s : State) (mem : ByteArray) (n bsize esize msize i w mask : Nat) :
    State :=
  { s with pc := UInt256.ofNat 1806
           stack := bitStack n bsize esize msize i w mask
           memory := mem }

/-- pc 1815, the multiply branch. -/
def ebitMul (s : State) (mem : ByteArray) (n bsize esize msize i w mask : Nat) :
    State :=
  { s with pc := UInt256.ofNat 1815
           stack := bitStack n bsize esize msize i w mask
           memory := mem }

/-- pc 1831, back from the multiply. -/
def ebitJoin (s : State) (mem : ByteArray) (n bsize esize msize i w mask : Nat) :
    State :=
  { s with pc := UInt256.ofNat 1831
           stack := bitStack n bsize esize msize i w mask
           memory := mem }

/-- `ENX`, pc 1832. -/
def ebitNext (s : State) (mem : ByteArray) (n bsize esize msize i w mask : Nat) :
    State :=
  { s with pc := UInt256.ofNat 1832
           stack := bitStack n bsize esize msize i w mask
           memory := mem }

/-- pc 1841, the byte-loop tail. -/
def ebTail (s : State) (mem : ByteArray) (n bsize esize msize i w : Nat) : State :=
  { s with pc := UInt256.ofNat 1841
           stack := bitStack n bsize esize msize i w 0
           memory := mem }

/-- `EBE`, pc 1850. -/
def ebEnd (s : State) (mem : ByteArray) (n bsize esize msize i : Nat) : State :=
  { s with pc := UInt256.ofNat 1850
           stack := UInt256.ofNat i :: outer n bsize esize msize
           memory := mem }

/-- pc 1876, back from the final `MonPro(ACC, ONE)`. -/
def finHead (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 1876
           stack := outer n bsize esize msize
           memory := mem }

/-- The halted state after `RETURN`. -/
def returnedState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) :
    State :=
  { s with pc := UInt256.ofNat 1885
           stack := outer n bsize esize msize
           memory := mem
           halt := .Returned
           hReturn := MachineState.readPadded mem (1024 + 32 * n - msize) msize }

set_option linter.unusedSimpArgs false in
/-- `blk1265` (pc 1756..1768): `MCOPY(ACC, R1, s32)` and start the byte loop. -/
theorem run_bDone (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hact : 298 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1265
      (bDone s mem n bsize esize msize) =
      some (ebHead s (mcopyMem mem 1024 4096 (32 * n)) n bsize esize msize 0) := by
  have hmod : (32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 32 * n :=
    mod_word_self (Nat.lt_of_le_of_lt (show 32 * n ≤ 1024 by omega) (by norm_num))
  have hfix1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      9344 32) = s.activeWords :=
    activeWords_fix s 9344 32 (by omega) (by omega) hact
  have hfix2 : UInt256.ofNat (MachineState.activeWordsAfter
      (MachineState.activeWordsAfter s.activeWords.toNat 1024 (32 * n)) 4096
      (32 * n)) = s.activeWords :=
    activeWords_fix2 s 1024 (32 * n) 4096 (32 * n) (by omega) (by omega) (by omega)
      (by omega) hact
  simp (config := { maxSteps := 600000 }) [blk1265, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    bDone, ebHead, mcopyMem, outer, hrun, hs32, hmod, hfix1, hfix2, push0_word,
    State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1272` (pc 1769..1777) with `i < esize`: process byte `i`. -/
theorem run_ebHead_body (s : State) (mem : ByteArray) (n bsize esize msize i : Nat)
    (he : esize ≤ 1024) (hi : i < esize) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1272
      (ebHead s mem n bsize esize msize i) =
      some (ebLoad s mem n bsize esize msize i) := by
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat esize) = UInt256.ofNat 1 :=
    lt_ofNat_of_lt (Nat.lt_of_lt_of_le hi (Nat.le_trans he (by norm_num)))
      (Nat.lt_of_le_of_lt he (by norm_num)) hi
  simp (config := { maxSteps := 400000 }) [blk1272, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ebHead, ebLoad, outer, hrun, hlt, isZero_ofNat_one, not_isTrue_zero,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1272` (pc 1769..1777) with `esize ≤ i`: leave the byte loop. -/
theorem run_ebHead_exit (s : State) (mem : ByteArray) (n bsize esize msize i : Nat)
    (he : esize ≤ 1024) (hi : i ≤ 1024) (hie : esize ≤ i)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1272
      (ebHead s mem n bsize esize msize i) =
      some (ebEnd s mem n bsize esize msize i) := by
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat esize) = UInt256.ofNat 0 :=
    lt_ofNat_of_le (Nat.lt_of_le_of_lt hi (by norm_num))
      (Nat.lt_of_le_of_lt he (by norm_num)) hie
  have h1850Nat : (UInt256.ofNat 1850).toNat = 1850 := by decide
  simp (config := { maxSteps := 400000 }) [blk1272, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ebHead, ebEnd, outer, hcode, hrun, hlt, isZero_ofNat_zero, isTrue_one,
    h1850Nat, jumpDest1850,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

/-- `blk1279` (pc 1778..1781): the tail call into `LZ`, which loads exponent
byte `i` and picks the mask the bit loop starts from. -/
theorem run_ebLoad (s : State) (mem : ByteArray)
    (n bsize esize msize i : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1279
      (ebLoad s mem n bsize esize msize i) =
      some (Lz.lzEntry s mem i (outer n bsize esize msize)) := by
  simp (config := { maxSteps := 400000 }) [blk1279, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ebLoad, Lz.lzEntry, hrun, hcode, jumpDest2922,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat]

/-- The mask the bit loop starts from: the byte's highest set bit for byte `0`,
`0x80` for every other byte. -/
def lzMask (input : ByteArray) (bsize i : Nat) : Nat :=
  if i = 0 then Lz.topBit (expByte input bsize i) else 128

set_option linter.unusedSimpArgs false in
/-- `blk1287` (pc 1789..1805): square `ACC`. -/
theorem run_ebitHead (s : State) (mem : ByteArray)
    (n bsize esize msize i w mask : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1287
      (ebitHead s mem n bsize esize msize i w mask) =
      some (mpCall s mem 1024 1024 1024 (UInt256.ofNat 1806)
        (bitStack n bsize esize msize i w mask)) := by
  have h1939Nat : (UInt256.ofNat 1939).toNat = 1939 := by decide
  simp (config := { maxSteps := 400000 }) [blk1287, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ebitHead, mpCall, bitStack, outer, hcode, hrun, h1939Nat, jumpDest1939,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1294` (pc 1806..1814) with the bit clear: skip the multiply. -/
theorem run_ebitTest_zero (s : State) (mem : ByteArray)
    (n bsize esize msize i w mask : Nat)
    (hmask : mask < 2 ^ 256) (hw : w < 2 ^ 256) (hand : mask &&& w = 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1294
      (ebitTest s mem n bsize esize msize i w mask) =
      some (ebitNext s mem n bsize esize msize i w mask) := by
  have hland : UInt256.land (UInt256.ofNat mask) (UInt256.ofNat w) =
      UInt256.ofNat 0 := by
    rw [land_ofNat mask w hmask hw, hand]
  have h1832Nat : (UInt256.ofNat 1832).toNat = 1832 := by decide
  simp (config := { maxSteps := 400000 }) [blk1294, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ebitTest, ebitNext, bitStack, outer, hcode, hrun, hland, isZero_ofNat_zero,
    isTrue_one, h1832Nat, jumpDest1832,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1294` (pc 1806..1814) with the bit set: fall into the multiply. -/
theorem run_ebitTest_one (s : State) (mem : ByteArray)
    (n bsize esize msize i w mask : Nat)
    (hmask : mask < 2 ^ 256) (hw : w < 2 ^ 256) (hand : mask &&& w ≠ 0)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1294
      (ebitTest s mem n bsize esize msize i w mask) =
      some (ebitMul s mem n bsize esize msize i w mask) := by
  have hland : UInt256.land (UInt256.ofNat mask) (UInt256.ofNat w) =
      UInt256.ofNat (mask &&& w) := land_ofNat mask w hmask hw
  have hzero : UInt256.isZero (UInt256.ofNat (mask &&& w)) = UInt256.ofNat 0 :=
    isZero_ofNat_of_ne (Nat.and_lt_two_pow mask hw) hand
  simp (config := { maxSteps := 400000 }) [blk1294, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ebitTest, ebitMul, bitStack, outer, hrun, hland, hzero, not_isTrue_zero,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1301` (pc 1815..1830): multiply `ACC` by `BASE`. -/
theorem run_ebitMul (s : State) (mem : ByteArray)
    (n bsize esize msize i w mask : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1301
      (ebitMul s mem n bsize esize msize i w mask) =
      some (mpCall s mem 1024 2048 1024 (UInt256.ofNat 1831)
        (bitStack n bsize esize msize i w mask)) := by
  have h1939Nat : (UInt256.ofNat 1939).toNat = 1939 := by decide
  simp (config := { maxSteps := 400000 }) [blk1301, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ebitMul, mpCall, bitStack, outer, hcode, hrun, h1939Nat, jumpDest1939,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1307` (pc 1831): the one-instruction rejoin. -/
theorem run_ebitJoin (s : State) (mem : ByteArray)
    (n bsize esize msize i w mask : Nat) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1307
      (ebitJoin s mem n bsize esize msize i w mask) =
      some (ebitNext s mem n bsize esize msize i w mask) := by
  simp (config := { maxSteps := 200000 }) [blk1307, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ebitJoin, ebitNext, bitStack, outer, hrun,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1308` (pc 1832..1840) with more bits to go: shift the mask and loop. -/
theorem run_ebitNext_loop (s : State) (mem : ByteArray)
    (n bsize esize msize i w mask : Nat) (hmask : 2 ≤ mask) (hmask256 : mask ≤ 128)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1308
      (ebitNext s mem n bsize esize msize i w mask) =
      some (ebitHead s mem n bsize esize msize i w (mask / 2)) := by
  have hshr : UInt256.shiftRight (UInt256.ofNat mask) (UInt256.ofNat 1) =
      UInt256.ofNat (mask / 2 ^ 1) :=
    shr_ofNat mask 1 (Nat.lt_of_le_of_lt hmask256 (by norm_num)) (by omega)
  have hp : mask / 2 ^ 1 = mask / 2 := by norm_num
  have htrue : UInt256.isTrue (UInt256.ofNat (mask / 2)) :=
    isTrue_ofNat (Nat.lt_of_le_of_lt (show mask / 2 ≤ 128 by omega) (by norm_num))
      (by omega)
  have h1789Nat : (UInt256.ofNat 1789).toNat = 1789 := by decide
  simp (config := { maxSteps := 400000 }) [blk1308, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ebitNext, ebitHead, bitStack, outer, hcode, hrun, hshr, hp, htrue, h1789Nat,
    jumpDest1789,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1308` (pc 1832..1840) after the last bit: leave the bit loop. -/
theorem run_ebitNext_exit (s : State) (mem : ByteArray)
    (n bsize esize msize i w : Nat) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1308
      (ebitNext s mem n bsize esize msize i w 1) =
      some (ebTail s mem n bsize esize msize i w) := by
  have hshr : UInt256.shiftRight (UInt256.ofNat 1) (UInt256.ofNat 1) =
      UInt256.ofNat 0 := by
    rw [shr_ofNat 1 1 (by norm_num) (by norm_num)]
    norm_num
  simp (config := { maxSteps := 400000 }) [blk1308, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ebitNext, ebTail, bitStack, outer, hrun, hshr, not_isTrue_zero,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1314` (pc 1841..1849): advance to the next exponent byte. -/
theorem run_ebTail (s : State) (mem : ByteArray) (n bsize esize msize i w : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1314
      (ebTail s mem n bsize esize msize i w) =
      some (ebHead s mem n bsize esize msize (i + 1)) := by
  have hcomm : 1 + i = i + 1 := Nat.add_comm 1 i
  have h1769Nat : (UInt256.ofNat 1769).toNat = 1769 := by decide
  simp (config := { maxSteps := 400000 }) [blk1314, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ebTail, ebHead, bitStack, outer, hcode, hrun, hcomm, h1769Nat, jumpDest1769,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1320` (pc 1850..1875): set `ONE` to one and call `MonPro(ACC, ONE)`. -/
theorem run_ebEnd (s : State) (mem : ByteArray) (n bsize esize msize i : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hact : 298 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1320
      (ebEnd s mem n bsize esize msize i) =
      some (mpCall s (storeWord mem (3040 + 32 * n) (UInt256.ofNat 1))
        1024 3072 1024 (UInt256.ofNat 1876) (outer n bsize esize msize)) := by
  have hmod : (3040 + 32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 3040 + 32 * n :=
    mod_word_self (Nat.lt_of_le_of_lt (show 3040 + 32 * n ≤ 4064 by omega)
      (by norm_num))
  have hfix : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (3040 + 32 * n) 32) = s.activeWords :=
    activeWords_fix s (3040 + 32 * n) 32 (by omega) (by omega) hact
  have h1939Nat : (UInt256.ofNat 1939).toNat = 1939 := by decide
  simp (config := { maxSteps := 600000 }) [blk1320, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ebEnd, mpCall, storeWord, outer, hcode, hrun, hmod, hfix, h1939Nat,
    jumpDest1939, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1333` (pc 1876..1885): `RETURN(ACC + s32 - msize, msize)`. -/
theorem run_return (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hm : 32 < msize) (hm32 : msize ≤ 32 * n)
    (hact : 298 ≤ s.activeWords.toNat) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1333
      (finHead s mem n bsize esize msize) =
      some (returnedState s mem n bsize esize msize) := by
  have hsub : UInt256.ofNat (1024 + 32 * n) - UInt256.ofNat msize =
      UInt256.ofNat (1024 + 32 * n - msize) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega)
      (Nat.lt_of_le_of_lt (show 1024 + 32 * n ≤ 2048 by omega) (by norm_num))
  have hmodOff : (1024 + 32 * n - msize) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 1024 + 32 * n - msize :=
    mod_word_self (Nat.lt_of_le_of_lt
      (show 1024 + 32 * n - msize ≤ 2048 by omega) (by norm_num))
  have hmodSz : msize %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = msize :=
    mod_word_self (Nat.lt_of_le_of_lt (show msize ≤ 1024 by omega) (by norm_num))
  have hfix : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (1024 + 32 * n - msize) msize) = s.activeWords :=
    activeWords_fix s (1024 + 32 * n - msize) msize (by omega) (by omega) hact
  simp (config := { maxSteps := 600000 }) [blk1333, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    finHead, returnedState, outer, hrun, hsub, hmodOff, hmodSz, hfix,
    State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

/-! ### Gas traces for the exponent blocks -/

def gasSteps_bDone (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hact : 298 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (bDone s mem n bsize esize msize)
      (ebHead s (mcopyMem mem 1024 4096 (32 * n)) n bsize esize msize 0) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1265 hcode hfork
      (run_bDone s mem n bsize esize msize hn hn32 hact hs32 hrun) hrun hnp

def gasSteps_ebHeadBody (s : State) (mem : ByteArray)
    (n bsize esize msize i : Nat) (he : esize ≤ 1024) (hi : i < esize)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (ebHead s mem n bsize esize msize i)
      (ebLoad s mem n bsize esize msize i) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1272 hcode hfork
      (run_ebHead_body s mem n bsize esize msize i he hi hrun) hrun hnp

def gasSteps_ebHeadExit (s : State) (mem : ByteArray)
    (n bsize esize msize i : Nat) (he : esize ≤ 1024) (hi : i ≤ 1024)
    (hie : esize ≤ i)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (ebHead s mem n bsize esize msize i)
      (ebEnd s mem n bsize esize msize i) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1272 hcode hfork
      (run_ebHead_exit s mem n bsize esize msize i he hi hie hcode hrun) hrun hnp

def gasSteps_ebLoad (s : State) (mem input : ByteArray)
    (n bsize esize msize i : Nat)
    (hdata : s.executionEnv.calldata = input)
    (hb : bsize ≤ 1024) (hi : i ≤ 1024) (hact : 298 ≤ s.activeWords.toNat)
    (heoff : MachineState.readWord mem 9472 = UInt256.ofNat (96 + bsize))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (ebLoad s mem n bsize esize msize i)
      (ebitHead s mem n bsize esize msize i (expByte input bsize i)
        (lzMask input bsize i)) :=
  have hlen : (outer n bsize esize msize).length ≤ 1008 := by
    simp only [outer, List.length_cons, List.length_nil]; omega
  have hbyte : UInt256.byteAt ⟨0⟩ (MachineState.readWord input (96 + bsize + i)) =
      UInt256.ofNat (expByte input bsize i) :=
    Challenge.EvmProof.Bytes.byteAt_zero_readWord input (96 + bsize + i)
  have hw : expByte input bsize i < 256 :=
    (YulSemantics.EVM.byteFrom input.toList (96 + bsize + i)).toNat_lt
  have g0 : Challenge.EvmProof.GasSteps (ebLoad s mem n bsize esize msize i)
      (Lz.lzEntry s mem i (outer n bsize esize msize)) :=
    Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka blk1279 hcode hfork
      (run_ebLoad s mem n bsize esize msize i hcode hrun) hrun hnp
  if h : i = 0 then
    have g1 : Challenge.EvmProof.GasSteps
        (Lz.lzEntry s mem i (outer n bsize esize msize))
        (Lz.lzFirst s mem i (expByte input bsize i) (outer n bsize esize msize)) :=
      Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka blk1781 hcode hfork
        (Lz.run_lzHead_first s mem input bsize i (expByte input bsize i)
          (outer n bsize esize msize) hlen hdata hb hi hact heoff hbyte hcode hrun h)
        hrun hnp
    have g2 : Challenge.EvmProof.GasSteps
        (Lz.lzFirst s mem i (expByte input bsize i) (outer n bsize esize msize))
        (Lz.lzJoin s mem i (expByte input bsize i)
          (Lz.topBit (expByte input bsize i)) (outer n bsize esize msize)) :=
      Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka blk1796 hcode hfork
        (Lz.run_lzFirst s mem i (expByte input bsize i) (outer n bsize esize msize)
          hlen hw hcode hrun) hrun hnp
    Challenge.EvmProof.GasSteps.cast ((g0.trans g1).trans g2) rfl
      (by simp only [lzMask, if_pos h, ebitHead, Lz.lzJoin, bitStack])
  else
    have g1 : Challenge.EvmProof.GasSteps
        (Lz.lzEntry s mem i (outer n bsize esize msize))
        (Lz.lzOther s mem i (expByte input bsize i) (outer n bsize esize msize)) :=
      Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka blk1781 hcode hfork
        (Lz.run_lzHead_other s mem input bsize i (expByte input bsize i)
          (outer n bsize esize msize) hlen hdata hb hi hact heoff hbyte hcode hrun h)
        hrun hnp
    have g2 : Challenge.EvmProof.GasSteps
        (Lz.lzOther s mem i (expByte input bsize i) (outer n bsize esize msize))
        (Lz.lzJoin s mem i (expByte input bsize i) 128
          (outer n bsize esize msize)) :=
      Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka blk1793 hcode hfork
        (Lz.run_lzOther s mem i (expByte input bsize i) (outer n bsize esize msize)
          hlen hcode hrun) hrun hnp
    Challenge.EvmProof.GasSteps.cast ((g0.trans g1).trans g2) rfl
      (by simp only [lzMask, if_neg h, ebitHead, Lz.lzJoin, bitStack])

def gasSteps_ebitHead (s : State) (mem : ByteArray)
    (n bsize esize msize i w mask : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (ebitHead s mem n bsize esize msize i w mask)
      (mpCall s mem 1024 1024 1024 (UInt256.ofNat 1806)
        (bitStack n bsize esize msize i w mask)) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1287 hcode hfork
      (run_ebitHead s mem n bsize esize msize i w mask hcode hrun) hrun hnp

def gasSteps_ebitTestZero (s : State) (mem : ByteArray)
    (n bsize esize msize i w mask : Nat)
    (hmask : mask < 2 ^ 256) (hw : w < 2 ^ 256) (hand : mask &&& w = 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (ebitTest s mem n bsize esize msize i w mask)
      (ebitNext s mem n bsize esize msize i w mask) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1294 hcode hfork
      (run_ebitTest_zero s mem n bsize esize msize i w mask hmask hw hand hcode hrun)
      hrun hnp

def gasSteps_ebitTestOne (s : State) (mem : ByteArray)
    (n bsize esize msize i w mask : Nat)
    (hmask : mask < 2 ^ 256) (hw : w < 2 ^ 256) (hand : mask &&& w ≠ 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (ebitTest s mem n bsize esize msize i w mask)
      (ebitMul s mem n bsize esize msize i w mask) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1294 hcode hfork
      (run_ebitTest_one s mem n bsize esize msize i w mask hmask hw hand hrun) hrun hnp

def gasSteps_ebitMul (s : State) (mem : ByteArray)
    (n bsize esize msize i w mask : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (ebitMul s mem n bsize esize msize i w mask)
      (mpCall s mem 1024 2048 1024 (UInt256.ofNat 1831)
        (bitStack n bsize esize msize i w mask)) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1301 hcode hfork
      (run_ebitMul s mem n bsize esize msize i w mask hcode hrun) hrun hnp

def gasSteps_ebitJoin (s : State) (mem : ByteArray)
    (n bsize esize msize i w mask : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (ebitJoin s mem n bsize esize msize i w mask)
      (ebitNext s mem n bsize esize msize i w mask) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1307 hcode hfork
      (run_ebitJoin s mem n bsize esize msize i w mask hrun) hrun hnp

def gasSteps_ebitNextLoop (s : State) (mem : ByteArray)
    (n bsize esize msize i w mask : Nat) (hmask : 2 ≤ mask) (hmask128 : mask ≤ 128)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (ebitNext s mem n bsize esize msize i w mask)
      (ebitHead s mem n bsize esize msize i w (mask / 2)) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1308 hcode hfork
      (run_ebitNext_loop s mem n bsize esize msize i w mask hmask hmask128 hcode hrun)
      hrun hnp

def gasSteps_ebitNextExit (s : State) (mem : ByteArray)
    (n bsize esize msize i w : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (ebitNext s mem n bsize esize msize i w 1)
      (ebTail s mem n bsize esize msize i w) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1308 hcode hfork
      (run_ebitNext_exit s mem n bsize esize msize i w hrun) hrun hnp

def gasSteps_ebTail (s : State) (mem : ByteArray) (n bsize esize msize i w : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (ebTail s mem n bsize esize msize i w)
      (ebHead s mem n bsize esize msize (i + 1)) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1314 hcode hfork
      (run_ebTail s mem n bsize esize msize i w hcode hrun) hrun hnp

def gasSteps_ebEnd (s : State) (mem : ByteArray) (n bsize esize msize i : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hact : 298 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (ebEnd s mem n bsize esize msize i)
      (mpCall s (storeWord mem (3040 + 32 * n) (UInt256.ofNat 1))
        1024 3072 1024 (UInt256.ofNat 1876) (outer n bsize esize msize)) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1320 hcode hfork
      (run_ebEnd s mem n bsize esize msize i hn hn32 hact hcode hrun) hrun hnp

def gasSteps_return (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hm : 32 < msize) (hm32 : msize ≤ 32 * n)
    (hact : 298 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (finHead s mem n bsize esize msize)
      (returnedState s mem n bsize esize msize) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1333 hcode hfork
      (run_return s mem n bsize esize msize hn hn32 hm hm32 hact hrun) hrun hnp

/-! ### Bit arithmetic for the exponent loop -/

theorem bitAt_eq_zero_iff (w r : Nat) : bitAt w r = 0 ↔ w.testBit r = false := by
  rw [bitAt, Model.bit_eq_testBit]
  cases w.testBit r <;> simp

theorem and_two_pow_eq_zero_iff (w r : Nat) :
    2 ^ r &&& w = 0 ↔ w.testBit r = false := by
  constructor
  · intro h
    have h2 : (2 ^ r &&& w).testBit r = false := by rw [h]; simp
    rw [Nat.testBit_and, Nat.testBit_two_pow_self] at h2
    simpa using h2
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hk : r = k
    · subst hk
      simp [h]
    · simp [hk]

theorem two_pow_ge_two {k : Nat} (hk : 1 ≤ k) : 2 ≤ 2 ^ k := by
  calc (2 : Nat) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

theorem two_pow_le_128 {k : Nat} (hk : k ≤ 7) : 2 ^ k ≤ 128 := by
  calc (2 : Nat) ^ k ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hk
    _ = 128 := by norm_num

theorem two_pow_shift {j : Nat} (hj : j < 7) :
    2 ^ (7 - j) / 2 = 2 ^ (7 - (j + 1)) := by
  have he : 7 - j = 7 - (j + 1) + 1 := by omega
  rw [he, pow_succ, Nat.mul_div_assoc _ (dvd_refl 2), Nat.div_self (by norm_num),
    Nat.mul_one]

/-! ### The bit loop -/

/-- The memory after one exponent bit. -/
def bitStep (mpMem : Nat → Nat → Nat → ByteArray → ByteArray) (mem : ByteArray) :
    Nat → ByteArray
  | 0 => mpMem 1024 1024 1024 mem
  | _ + 1 => mpMem 1024 2048 1024 (mpMem 1024 1024 1024 mem)

/-- The memory after `j` bits of the exponent byte `w`. -/
def bitMems (mpMem : Nat → Nat → Nat → ByteArray → ByteArray) (w : Nat)
    (mem : ByteArray) : Nat → ByteArray
  | 0 => mem
  | j + 1 => bitStep mpMem (bitMems mpMem w mem j) (bitAt w (7 - j))

/-- The memory after all eight bits of the exponent byte `w`. -/
def byteMem (mpMem : Nat → Nat → Nat → ByteArray → ByteArray) (w : Nat)
    (mem : ByteArray) : ByteArray := bitMems mpMem w mem 8

/-- The memory after `k` bits of exponent byte `w`, started at bit index `j0`. -/
def bitMemsFrom (mpMem : Nat → Nat → Nat → ByteArray → ByteArray) (w : Nat)
    (mem : ByteArray) (j0 : Nat) : Nat → ByteArray
  | 0 => mem
  | k + 1 => bitStep mpMem (bitMemsFrom mpMem w mem j0 k) (bitAt w (7 - (j0 + k)))

/-- How many leading bits of exponent byte `i` the loop skips: byte `0` starts
at its highest set bit, every other byte at bit 7. -/
def lzSkip (input : ByteArray) (bsize i : Nat) : Nat :=
  if i = 0 then 7 - Lz.topExp (expByte input bsize i) else 0

theorem lzSkip_le (input : ByteArray) (bsize i : Nat) : lzSkip input bsize i ≤ 7 := by
  unfold lzSkip; split <;> omega

/-- The memory after exponent byte `i`, with its leading bits skipped. -/
def byteMemAt (mpMem : Nat → Nat → Nat → ByteArray → ByteArray) (input : ByteArray)
    (bsize : Nat) (mem : ByteArray) (i : Nat) : ByteArray :=
  bitMemsFrom mpMem (expByte input bsize i) mem (lzSkip input bsize i)
    (8 - lzSkip input bsize i)

/-- The memory after `i` exponent bytes. -/
def ebMems (mpMem : Nat → Nat → Nat → ByteArray → ByteArray) (input : ByteArray)
    (bsize : Nat) (mem : ByteArray) : Nat → ByteArray
  | 0 => mem
  | i + 1 => byteMemAt mpMem input bsize (ebMems mpMem input bsize mem i) i

def bitFamily (s : State) (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (mem : ByteArray) (n bsize esize msize i w j : Nat) : State :=
  ebitHead s (bitMems mpMem w mem j) n bsize esize msize i w (2 ^ (7 - j))


/-! ### Preservation of `V_EOFF` across the exponent loop -/

theorem readWord_bitStep (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (addr : Nat)
    (hkeep : ∀ (pa pb : Nat) (mem' : ByteArray),
      MachineState.readWord (mpMem pa pb 1024 mem') addr =
        MachineState.readWord mem' addr)
    (mem : ByteArray) (bit : Nat) :
    MachineState.readWord (bitStep mpMem mem bit) addr =
      MachineState.readWord mem addr := by
  cases bit with
  | zero => exact hkeep 1024 1024 mem
  | succ k =>
      show MachineState.readWord (mpMem 1024 2048 1024 (mpMem 1024 1024 1024 mem))
        addr = _
      rw [hkeep 1024 2048 _, hkeep 1024 1024 mem]

theorem readWord_bitMems (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (addr : Nat)
    (hkeep : ∀ (pa pb : Nat) (mem' : ByteArray),
      MachineState.readWord (mpMem pa pb 1024 mem') addr =
        MachineState.readWord mem' addr)
    (w : Nat) (mem : ByteArray) (j : Nat) :
    MachineState.readWord (bitMems mpMem w mem j) addr =
      MachineState.readWord mem addr := by
  induction j with
  | zero => rfl
  | succ j ih =>
      show MachineState.readWord (bitStep mpMem (bitMems mpMem w mem j)
        (bitAt w (7 - j))) addr = _
      rw [readWord_bitStep mpMem addr hkeep, ih]

theorem readWord_bitMemsFrom (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (addr : Nat)
    (hkeep : ∀ (pa pb : Nat) (mem' : ByteArray),
      MachineState.readWord (mpMem pa pb 1024 mem') addr =
        MachineState.readWord mem' addr)
    (w : Nat) (mem : ByteArray) (j0 k : Nat) :
    MachineState.readWord (bitMemsFrom mpMem w mem j0 k) addr =
      MachineState.readWord mem addr := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show MachineState.readWord (bitStep mpMem (bitMemsFrom mpMem w mem j0 k)
        (bitAt w (7 - (j0 + k)))) addr = _
      rw [readWord_bitStep mpMem addr hkeep _ _, ih]

theorem readWord_ebMems (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (addr : Nat)
    (hkeep : ∀ (pa pb : Nat) (mem' : ByteArray),
      MachineState.readWord (mpMem pa pb 1024 mem') addr =
        MachineState.readWord mem' addr)
    (input : ByteArray) (bsize : Nat) (mem : ByteArray) (i : Nat) :
    MachineState.readWord (ebMems mpMem input bsize mem i) addr =
      MachineState.readWord mem addr := by
  induction i with
  | zero => rfl
  | succ i ih =>
      show MachineState.readWord (byteMemAt mpMem input bsize
        (ebMems mpMem input bsize mem i) i) addr = _
      rw [byteMemAt, readWord_bitMemsFrom mpMem addr hkeep, ih]

/-- The indexed byte-loop family. -/
def ebFamily (s : State) (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (input mem : ByteArray) (n bsize esize msize i : Nat) : State :=
  ebHead s (ebMems mpMem input bsize mem i) n bsize esize msize i


/-! ## The returned byte string

`RETURN(ACC + s32 - msize, msize)` slices the last `msize` bytes of the `ACC`
block.  Because the block is a big-endian `32 * n`-byte encoding, that slice is
exactly the big-endian `msize`-byte encoding of the value it holds — and the
`32 * n - msize` bytes it drops are all zero. -/

theorem byteFrom_eq_getD (bs : ByteArray) (i : Nat) :
    YulSemantics.EVM.byteFrom bs.toList i = bs[i]?.getD 0 := by
  unfold YulSemantics.EVM.byteFrom
  rw [List.getD_eq_getElem?_getD, YulEvmCompiler.ByteArray.toList_eq_data,
    Array.getElem?_toList]
  rfl

theorem memoryLimbs_succ (mem : ByteArray) (ptr count : Nat) :
    Limbs.memoryLimbs mem ptr (count + 1) =
      (MachineState.readWord mem ptr).toNat ::
        Limbs.memoryLimbs mem (ptr + 32) count := by
  apply List.ext_getElem
  · simp
  · intro k hk _
    have hk1 : k < count + 1 := by simpa using hk
    cases k with
    | zero => simp [Limbs.memoryLimbs]
    | succ j =>
        have hj : j < count := by omega
        simp only [Limbs.memoryLimbs, List.getElem_cons_succ, List.getElem_map,
          List.getElem_range]
        rw [show ptr + 32 * (j + 1) = ptr + 32 + 32 * j from by omega]

theorem fastLimbs_succ (mem : ByteArray) (ptr count : Nat) :
    Model.fastLimbs mem ptr (count + 1) =
      Model.fastLimbs mem (ptr + 32) count ++
        [(MachineState.readWord mem ptr).toNat] := by
  rw [Model.fastLimbs_eq_reverse_memoryLimbs, Model.fastLimbs_eq_reverse_memoryLimbs,
    memoryLimbs_succ, List.reverse_cons]

/-- The `32 * count` bytes of a limb block, read big-endian, are its value. -/
theorem bytesToNatPadded_block (mem : ByteArray) : ∀ (count ptr : Nat),
    Precompile.bytesToNatPadded mem ptr (32 * count) =
      Nat.ofDigits Limbs.radix (Model.fastLimbs mem ptr count) := by
  intro count
  induction count with
  | zero => intro ptr; simp [Model.fastLimbs]
  | succ c ih =>
      intro ptr
      have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add mem ptr 32 (32 * c)
      rw [show 32 + 32 * c = 32 * (c + 1) by ring] at hsplit
      rw [hsplit, fastLimbs_succ, Nat.ofDigits_append, Model.length_fastLimbs,
        ih (ptr + 32), Nat.ofDigits_singleton,
        ← Challenge.EvmProof.Bytes.readWord_toNat, ← Limbs.pow_radix]
      ring

theorem bytesToNatPadded_of_fastRepresents {mem : ByteArray} {ptr count value : Nat}
    (hrep : Model.FastRepresents mem ptr count value) :
    Precompile.bytesToNatPadded mem ptr (32 * count) = value := by
  rw [bytesToNatPadded_block mem count ptr, Model.value_of_fastRepresents hrep]

/-- **The dropped bytes are zero.**  A block holding a value below
`256 ^ msize` has `32 * count - msize` leading zero bytes. -/
theorem return_leading_zeros {mem : ByteArray} {ptr count value msize : Nat}
    (hrep : Model.FastRepresents mem ptr count value) (hm : msize ≤ 32 * count)
    (hlt : value < 256 ^ msize) :
    Precompile.bytesToNatPadded mem ptr (32 * count - msize) = 0 := by
  have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add mem ptr
    (32 * count - msize) msize
  rw [show 32 * count - msize + msize = 32 * count from by omega,
    bytesToNatPadded_of_fastRepresents hrep] at hsplit
  have htail := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow mem
    (ptr + (32 * count - msize)) msize
  by_contra hne
  have h1 : 1 ≤ Precompile.bytesToNatPadded mem ptr (32 * count - msize) :=
    Nat.pos_of_ne_zero hne
  have h2 : 1 * 256 ^ msize ≤
      Precompile.bytesToNatPadded mem ptr (32 * count - msize) * 256 ^ msize :=
    Nat.mul_le_mul_right _ h1
  rw [Nat.one_mul] at h2
  omega

/-- Byte `k` of a big-endian read. -/
theorem bytesToNatPadded_digit (bs : ByteArray) (off w k : Nat) (hk : k < w) :
    Precompile.bytesToNatPadded bs off w / 256 ^ (w - 1 - k) % 256 =
      (YulSemantics.EVM.byteFrom bs.toList (off + k)).toNat := by
  have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add bs off (k + 1)
    (w - (k + 1))
  rw [show k + 1 + (w - (k + 1)) = w from by omega] at hsplit
  have htail := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow bs (off + (k + 1))
    (w - (k + 1))
  have hsplit' : Precompile.bytesToNatPadded bs off w =
      256 ^ (w - (k + 1)) * Precompile.bytesToNatPadded bs off (k + 1) +
        Precompile.bytesToNatPadded bs (off + (k + 1)) (w - (k + 1)) := by
    rw [hsplit]; ring
  have hdiv : Precompile.bytesToNatPadded bs off w / 256 ^ (w - 1 - k) =
      Precompile.bytesToNatPadded bs off (k + 1) := by
    rw [show w - 1 - k = w - (k + 1) from by omega, hsplit',
      Nat.mul_add_div (pow_pos (by norm_num) _), Nat.div_eq_of_lt htail,
      Nat.add_zero]
  have hb : (YulSemantics.EVM.byteFrom bs.toList (off + k)).toNat < 256 :=
    (YulSemantics.EVM.byteFrom bs.toList (off + k)).toNat_lt
  rw [hdiv, Challenge.EvmProof.Bytes.bytesToNatPadded_succ bs off k]
  omega

theorem uint8_ofNat_toNat (b : UInt8) : UInt8.ofNat b.toNat = b := by
  simp

/-- **The returned slice.**  The last `msize` bytes of a block holding `value`
are the big-endian `msize`-byte encoding of `value`. -/
theorem readPadded_eq_natToBytes {mem : ByteArray} {ptr count value msize : Nat}
    (hrep : Model.FastRepresents mem ptr count value) (hm : msize ≤ 32 * count) :
    MachineState.readPadded mem (ptr + 32 * count - msize) msize =
      Precompile.natToBytes value msize := by
  apply ByteArray.ext_getElem
  · rw [Challenge.EvmProof.Memory.readPadded_size, Precompile.natToBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro k hleft hright
    have hk : k < msize := by
      simpa [Precompile.natToBytes,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hright
    have hdig := bytesToNatPadded_digit mem ptr (32 * count)
      (32 * count - msize + k) (by omega)
    rw [bytesToNatPadded_of_fastRepresents hrep,
      show 32 * count - 1 - (32 * count - msize + k) = msize - 1 - k from by omega]
      at hdig
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hk,
      Precompile.natToBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ msize k hk,
      show ptr + 32 * count - msize + k = ptr + (32 * count - msize + k) from by omega,
      ← byteFrom_eq_getD, hdig, uint8_ofNat_toNat]

/-- **The `RETURN` payload is the specification.** -/
theorem returned_eq_spec (s : State) (mem input : ByteArray)
    (n bsize esize msize result : Nat) (_hn : 2 ≤ n) (hm : msize ≤ 32 * n)
    (hmpos : 0 < msize)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hrep : Model.FastRepresents mem 1024 n result)
    (hres : result = Precompile.modPow
      (Precompile.bytesToNatPadded input 96 bsize)
      (Precompile.bytesToNatPadded input (96 + bsize) esize)
      (Precompile.bytesToNatPadded input (96 + bsize + esize) msize)) :
    (returnedState s mem n bsize esize msize).hReturn = Challenge.Modexp.spec input := by
  have hslice := readPadded_eq_natToBytes hrep hm
  have hspec : Challenge.Modexp.spec input =
      Precompile.natToBytes (Precompile.modPow
        (Precompile.bytesToNatPadded input 96 bsize)
        (Precompile.bytesToNatPadded input (96 + bsize) esize)
        (Precompile.bytesToNatPadded input (96 + bsize + esize) msize)) msize := by
    simp only [Challenge.Modexp.spec, ← hbsize, ← hesize, ← hmsz]
    exact if_neg (by omega)
  show MachineState.readPadded mem (1024 + 32 * n - msize) msize = _
  rw [hslice, hspec, hres]

/-! ## The exponent bridge

The bits the loop consumes are exactly the big-endian bits of
`Precompile.bytesToNatPadded input (96 + bsize) esize`. -/

/-- Exponent byte `i` is digit `i` of the exponent. -/
theorem expByte_eq_digit (input : ByteArray) (bsize esize i : Nat) (hi : i < esize) :
    expByte input bsize i =
      Precompile.bytesToNatPadded input (96 + bsize) esize /
        256 ^ (esize - 1 - i) % 256 :=
  (bytesToNatPadded_digit input (96 + bsize) esize i hi).symm

/-- Bit `r` of exponent byte `i` is bit `8 * (esize - 1 - i) + r` of the
exponent. -/
theorem bitAt_expByte (input : ByteArray) (bsize esize i r : Nat)
    (hi : i < esize) (hr : r < 8) :
    bitAt (expByte input bsize i) r =
      bitAt (Precompile.bytesToNatPadded input (96 + bsize) esize)
        (8 * (esize - 1 - i) + r) := by
  have h256 : (256 : Nat) ^ (esize - 1 - i) = 2 ^ (8 * (esize - 1 - i)) := by
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]
  have hsplit : (2 : Nat) ^ 8 = 2 ^ r * 2 ^ (8 - r) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [expByte_eq_digit input bsize esize i hi, bitAt, bitAt, h256,
    show (256 : Nat) = 2 ^ 8 by norm_num, hsplit, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega)), Nat.div_div_eq_div_mul,
    ← pow_add]

/-- The bit index the loop reaches at byte `i`, bit `j`. -/
theorem bit_index (esize i j : Nat) (hi : i < esize) (hj : j < 8) :
    8 * esize - (8 * i + j) - 1 = 8 * (esize - 1 - i) + (7 - j) := by
  omega

/-- One left-to-right step of the accumulated exponent. -/
theorem expPrefix_step (e B t : Nat) (ht : t < B) :
    Model.expPrefix e (B - t - 1) =
      2 * Model.expPrefix e (B - t) + bitAt e (B - t - 1) := by
  have h := Model.expPrefix_succ e (B - t - 1)
  rwa [show B - t - 1 + 1 = B - t from by omega] at h

/-- The accumulated exponent starts at zero. -/
theorem expPrefix_start (input : ByteArray) (bsize esize : Nat) :
    Model.expPrefix (Precompile.bytesToNatPadded input (96 + bsize) esize)
      (8 * esize) = 0 := by
  apply Model.expPrefix_top
  have h := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input (96 + bsize) esize
  rwa [show (256 : Nat) ^ esize = 2 ^ (8 * esize) by
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]] at h

/-- After all `8 * esize` bits the accumulated exponent is the exponent. -/
theorem expPrefix_end (input : ByteArray) (bsize esize : Nat) :
    Model.expPrefix (Precompile.bytesToNatPadded input (96 + bsize) esize) 0 =
      Precompile.bytesToNatPadded input (96 + bsize) esize :=
  Model.expPrefix_zero _


/-! ## The arithmetic of the three loops

Neither `MONPRO` nor `ADDMOD` has a functional contract in this module, so what
each loop computes is stated in the arithmetic model — `Model.montMul` for the
Montgomery product and `(a + b) % m` for the modular addition.  Composing these
recursions with `Fast.Monpro`'s and `Fast.Csub`'s correctness statements gives
the memory-level postconditions. -/

/-- The value the `RR` block holds after `i` iterations of the `RR` chain:
square, then multiply by `R1` or `CC` according to bit `5 - i` of `n`. -/
def rrValue (mm R n : Nat) : Nat → Nat
  | 0 => R % mm
  | i + 1 =>
      Model.montMul mm R
        (Model.montMul mm R (rrValue mm R n i) (rrValue mm R n i))
        (if bitAt n (5 - i) = 0 then R % mm else Limbs.radix * R % mm)

theorem rrValue_succ (mm R n i : Nat) :
    rrValue mm R n (i + 1) =
      Model.montMul mm R
        (Model.montMul mm R (rrValue mm R n i) (rrValue mm R n i))
        (if bitAt n (5 - i) = 0 then R % mm else Limbs.radix * R % mm) := rfl

/-- `R1` is the Montgomery form of one, so multiplying by it does nothing. -/
theorem montMul_by_one {mm R x : Nat} (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    (hx : x < mm) : Model.montMul mm R x (R % mm) = x :=
  Model.montMul_eq_of_modEq hm hcop
    (Nat.ModEq.mul_left x (Nat.mod_modEq R mm).symm) hx

/-- **The `RR` chain invariant.**  After `i` iterations the block holds the
Montgomery form of `radix ^ (n >>> (6 - i))`. -/
theorem rrValue_form {mm R : Nat} (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    {n : Nat} (hn : n ≤ 32) : ∀ i, i ≤ 6 →
    rrValue mm R n i ≡ Limbs.radix ^ (n / 2 ^ (6 - i)) * R [MOD mm] := by
  intro i
  induction i with
  | zero =>
      intro _
      have h64 : n / 2 ^ (6 - 0) = 0 := by
        apply Nat.div_eq_of_lt
        have : (2 : Nat) ^ (6 - 0) = 64 := by norm_num
        omega
      rw [h64, pow_zero, one_mul]
      exact Nat.mod_modEq R mm
  | succ i ih =>
      intro hi
      have hv := ih (by omega)
      have hsq := Model.montMul_form hm hcop hv hv
      have hpow : Limbs.radix ^ (n / 2 ^ (6 - i)) * Limbs.radix ^ (n / 2 ^ (6 - i)) =
          Limbs.radix ^ (2 * (n / 2 ^ (6 - i))) := by
        rw [two_mul, pow_add]
      have hx : Limbs.radix ^ (n / 2 ^ (6 - i)) * Limbs.radix ^ (n / 2 ^ (6 - i)) * R
          % mm ≡ Limbs.radix ^ (2 * (n / 2 ^ (6 - i))) * R [MOD mm] := by
        rw [hpow]
        exact Nat.mod_modEq _ mm
      have hsel : (if bitAt n (5 - i) = 0 then R % mm else Limbs.radix * R % mm) ≡
          Limbs.radix ^ bitAt n (5 - i) * R [MOD mm] := by
        by_cases h0 : bitAt n (5 - i) = 0
        · rw [if_pos h0, h0, pow_zero, one_mul]
          exact Nat.mod_modEq R mm
        · have h1 : bitAt n (5 - i) = 1 := by
            have := bitAt_le_one n (5 - i)
            omega
          rw [if_neg h0, h1, pow_one]
          exact Nat.mod_modEq _ mm
      have hstep : n / 2 ^ (6 - (i + 1)) =
          2 * (n / 2 ^ (6 - i)) + bitAt n (5 - i) := by
        have h := Model.expPrefix_succ n (5 - i)
        rw [show 6 - (i + 1) = 5 - i from by omega]
        rw [Model.expPrefix, Model.expPrefix,
          show 5 - i + 1 = 6 - i from by omega] at h
        exact h
      rw [rrValue_succ, hsq, Model.montMul_form hm hcop hx hsel, hstep, pow_add]
      exact Nat.mod_modEq _ mm

/-- **The `RR` chain postcondition.**  Six iterations leave the Montgomery form
of `radix ^ n`; taking `R = radix ^ n mod m` this is `R ^ 2 mod m`. -/
theorem rrValue_final {mm R : Nat} (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    {n : Nat} (hn : n ≤ 32) :
    rrValue mm R n 6 ≡ Limbs.radix ^ n * R [MOD mm] := by
  have h := rrValue_form hm hcop hn 6 le_rfl
  rwa [show (6 : Nat) - 6 = 0 from rfl, pow_zero, Nat.div_one] at h

/-- The value `ACC` holds after `t` Horner steps over the `pb` base limbs. -/
def blValue (mm b pb : Nat) : Nat → Nat
  | 0 => b / Limbs.radix ^ (pb - 1) % mm
  | t + 1 =>
      (blValue mm b pb t * Limbs.radix % mm +
        b / Limbs.radix ^ (pb - 1 - (t + 1)) % Limbs.radix) % mm

theorem blValue_succ (mm b pb t : Nat) :
    blValue mm b pb (t + 1) =
      (blValue mm b pb t * Limbs.radix % mm +
        b / Limbs.radix ^ (pb - 1 - (t + 1)) % Limbs.radix) % mm := rfl

/-- **The Horner invariant.**  After `t` steps the accumulator holds the top
`t + 1` limbs of the base, reduced. -/
theorem blValue_eq (mm b pb : Nat) : ∀ t, t < pb →
    blValue mm b pb t = b / Limbs.radix ^ (pb - 1 - t) % mm := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro ht
      have hk : pb - 1 - t = pb - 1 - (t + 1) + 1 := by omega
      rw [blValue_succ, ih (by omega), hk]
      exact Model.horner_div_step mm b (pb - 1 - (t + 1))

/-- **The base-chain postcondition.**  After `pb - 1` steps the accumulator is
`b mod m`. -/
theorem blValue_final (mm b pb : Nat) (hpb : 1 ≤ pb) :
    blValue mm b pb (pb - 1) = b % mm := by
  rw [blValue_eq mm b pb (pb - 1) (by omega),
    show pb - 1 - (pb - 1) = 0 from by omega, pow_zero, Nat.div_one]

/-- The accumulator after `t` exponent bits. -/
def expAcc (mm R bM : Nat) (bits : Nat → Nat) : Nat → Nat
  | 0 => R % mm
  | t + 1 =>
      if bits t = 0 then
        Model.montMul mm R (expAcc mm R bM bits t) (expAcc mm R bM bits t)
      else
        Model.montMul mm R
          (Model.montMul mm R (expAcc mm R bM bits t) (expAcc mm R bM bits t)) bM

theorem expAcc_succ (mm R bM : Nat) (bits : Nat → Nat) (t : Nat) :
    expAcc mm R bM bits (t + 1) =
      if bits t = 0 then
        Model.montMul mm R (expAcc mm R bM bits t) (expAcc mm R bM bits t)
      else
        Model.montMul mm R
          (Model.montMul mm R (expAcc mm R bM bits t) (expAcc mm R bM bits t)) bM :=
  rfl

/-- The exponent the loop has accumulated after `t` bits. -/
def expExp (bits : Nat → Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => 2 * expExp bits t + bits t

/-- **The exponent-loop invariant.**  The accumulator is the Montgomery form of
`b ^ E` for the exponent `E` accumulated so far. -/
theorem expAcc_form {mm R b bM : Nat} (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    (hbM : bM ≡ b * R [MOD mm]) (bits : Nat → Nat) (hbits : ∀ t, bits t ≤ 1) :
    ∀ t, expAcc mm R bM bits t ≡ b ^ expExp bits t * R [MOD mm] := by
  intro t
  induction t with
  | zero => exact Model.mont_pow_zero_form mm R b
  | succ t ih =>
      rw [expAcc_succ, Model.mont_bit_step hm hcop ih hbM (hbits t)]
      exact Nat.mod_modEq _ mm

/-- **The exponent bridge.**  Consuming the big-endian bits of `e` accumulates
exactly `e`. -/
theorem expExp_eq_prefix {e B : Nat} (he : e < 2 ^ B) (bits : Nat → Nat)
    (hbits : ∀ t, t < B → bits t = bitAt e (B - t - 1)) :
    ∀ t, t ≤ B → expExp bits t = Model.expPrefix e (B - t) := by
  intro t
  induction t with
  | zero => intro _; exact (Model.expPrefix_top he).symm
  | succ t ih =>
      intro ht
      show 2 * expExp bits t + bits t = _
      rw [ih (by omega), hbits t (by omega),
        show B - (t + 1) = B - t - 1 from by omega]
      exact (expPrefix_step e B t (by omega)).symm

theorem expExp_eq {e B : Nat} (he : e < 2 ^ B) (bits : Nat → Nat)
    (hbits : ∀ t, t < B → bits t = bitAt e (B - t - 1)) :
    expExp bits B = e := by
  have h := expExp_eq_prefix he bits hbits B le_rfl
  rwa [Nat.sub_self, Model.expPrefix_zero] at h

/-- **The final conversion.**  `MonPro(ACC, 1)` on the Montgomery form of
`b ^ e` yields the precompile's answer. -/
theorem expAcc_out {mm R b bM : Nat} (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    (hbM : bM ≡ b * R [MOD mm]) (bits : Nat → Nat) (hbits : ∀ t, bits t ≤ 1)
    {e B : Nat} (he : e < 2 ^ B)
    (hbit : ∀ t, t < B → bits t = bitAt e (B - t - 1)) :
    Model.montMul mm R (expAcc mm R bM bits B) 1 =
      Precompile.modPow b e mm := by
  have hform := expAcc_form hm hcop hbM bits hbits B
  rw [expExp_eq he bits hbit] at hform
  exact Model.mont_out_modPow hm hcop hform

/-! ## Memory-level postconditions of the three loops

The two subroutines enter through the functional contract `SubSpec`; composing
it with the value recursions above turns each loop's arithmetic invariant into
a statement about the named blocks. -/

/-- Functional contract for `MONPRO` and `ADDMOD` at `n` limbs, modulus `mm`.
`Fast.Monpro` and `Fast.Csub` supply it. -/
structure SubSpec (mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (n mm R minv : Nat) : Prop where
  /-- `MonPro(pa, pb) → pd` writes the Montgomery product.  The pointer bounds
  and the `V_MINV` word are exactly the memory-dependent hypotheses
  `Fast.Monpro.monpro_represents` takes; its constant side conditions
  (`2 ≤ n ≤ 32`, `m` odd, and `m % radix * minv + 1 ≡ 0 [MOD 2 ^ 256]`) are
  supplied once by whoever builds this record. -/
  mpValue : ∀ (pa pb pd : Nat) (mem : ByteArray) (a b : Nat),
    pa + 32 * n ≤ 8192 → pb + 32 * n ≤ 8192 → pd + 32 * n ≤ 8192 →
    Model.FastRepresents mem 0 n mm →
    MachineState.readWord mem 9376 = UInt256.ofNat minv →
    Model.FastRepresents mem pa n a → Model.FastRepresents mem pb n b →
    a < mm → b < mm →
    Model.FastRepresents (mpMem pa pb pd mem) pd n (Model.montMul mm R a b)
  /-- `MonPro` leaves every other named block alone. -/
  mpFrame : ∀ (pa pb pd ptr v : Nat) (mem : ByteArray),
    ptr + 32 * n ≤ 7168 → (pd + 32 * n ≤ ptr ∨ ptr + 32 * n ≤ pd) →
    Model.FastRepresents mem ptr n v →
    Model.FastRepresents (mpMem pa pb pd mem) ptr n v
  /-- `MonPro` writes nothing at or above `V_MINV = 0x24A0`. -/
  mpMinv : ∀ (pa pb pd : Nat) (mem : ByteArray), pd ≤ 6144 →
    MachineState.readWord (mpMem pa pb pd mem) 9376 = MachineState.readWord mem 9376
  /-- `AddMod(pa, pb) → pd` writes the modular sum. -/
  amValue : ∀ (pa pb pd : Nat) (mem : ByteArray) (a b : Nat),
    pa + 32 * n ≤ 8192 → pb + 32 * n ≤ 8192 → pd + 32 * n ≤ 8192 →
    Model.FastRepresents mem 0 n mm →
    Model.FastRepresents mem pa n a → Model.FastRepresents mem pb n b →
    a + b < 2 * mm →
    Model.FastRepresents (amMem pa pb pd mem) pd n ((a + b) % mm)
  /-- `AddMod` leaves every other named block alone. -/
  amFrame : ∀ (pa pb pd ptr v : Nat) (mem : ByteArray),
    ptr + 32 * n ≤ 7168 → (pd + 32 * n ≤ ptr ∨ ptr + 32 * n ≤ pd) →
    Model.FastRepresents mem ptr n v →
    Model.FastRepresents (amMem pa pb pd mem) ptr n v
  /-- `AddMod` writes nothing at or above `V_MINV = 0x24A0`. -/
  amMinv : ∀ (pa pb pd : Nat) (mem : ByteArray), pd ≤ 6144 →
    MachineState.readWord (amMem pa pb pd mem) 9376 = MachineState.readWord mem 9376

theorem rrValue_lt {mm R n : Nat} (hm : 0 < mm) : ∀ i, rrValue mm R n i < mm := by
  intro i
  cases i with
  | zero => exact Nat.mod_lt _ hm
  | succ i => exact Model.montMul_lt hm _ _ _

/-- The four blocks the `RR` chain reads and writes. -/
structure RrInv (mem : ByteArray) (n mm R v : Nat) : Prop where
  modulus : Model.FastRepresents mem 0 n mm
  r1 : Model.FastRepresents mem 4096 n (R % mm)
  cc : Model.FastRepresents mem 5120 n (Limbs.radix * R % mm)
  rr : Model.FastRepresents mem 6144 n v

/-- `V_MINV` survives the `RR` chain. -/
theorem readWord_rrMem (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (hkeep : ∀ (pa pb : Nat) (mem' : ByteArray),
      MachineState.readWord (mpMem pa pb 6144 mem') 9376 =
        MachineState.readWord mem' 9376)
    (n : Nat) (mem : ByteArray) (i : Nat) :
    MachineState.readWord (rrMem mpMem n mem i) 9376 =
      MachineState.readWord mem 9376 := by
  induction i with
  | zero => rfl
  | succ i ih =>
      show MachineState.readWord (rrStep mpMem n (5 - i) (rrMem mpMem n mem i))
        9376 = _
      unfold rrStep
      split
      · rw [hkeep 6144 6144 _, ih]
      · rw [hkeep 6144 5120 _, hkeep 6144 6144 _, ih]

set_option maxHeartbeats 16000000 in
/-- **The `RR` chain, at the level of memory.** -/
theorem rrMem_inv {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hcop : Nat.Coprime R mm)
    (hn32 : n ≤ 32) (mem : ByteArray)
    (hminv : MachineState.readWord mem 9376 = UInt256.ofNat minv)
    (hinv : RrInv mem n mm R (R % mm)) : ∀ i,
    RrInv (rrMem mpMem n mem i) n mm R (rrValue mm R n i) := by
  intro i
  induction i with
  | zero => exact hinv
  | succ i ih =>
      have hv : rrValue mm R n i < mm := rrValue_lt hm i
      have hsellb : selOf n (5 - i) ≤ 5120 := by
        have := bitAt_le_one n (5 - i)
        unfold selOf
        omega
      have hmi : MachineState.readWord (rrMem mpMem n mem i) 9376 =
          UInt256.ofNat minv :=
        (readWord_rrMem mpMem
          (fun pa pb m => spec.mpMinv pa pb 6144 m (by omega)) n mem i).trans hminv
      have hmi1 : MachineState.readWord
          (mpMem 6144 6144 6144 (rrMem mpMem n mem i)) 9376 = UInt256.ofNat minv :=
        (spec.mpMinv 6144 6144 6144 _ (by omega)).trans hmi
      have hsq : Model.FastRepresents (mpMem 6144 6144 6144 (rrMem mpMem n mem i))
          6144 n (Model.montMul mm R (rrValue mm R n i) (rrValue mm R n i)) :=
        spec.mpValue 6144 6144 6144 _ _ _ (by omega) (by omega) (by omega)
          ih.modulus hmi ih.rr ih.rr hv hv
      have hmod1 : Model.FastRepresents (mpMem 6144 6144 6144 (rrMem mpMem n mem i))
          0 n mm :=
        spec.mpFrame 6144 6144 6144 0 mm _ (by omega) (Or.inr (by omega)) ih.modulus
      have hr11 : Model.FastRepresents (mpMem 6144 6144 6144 (rrMem mpMem n mem i))
          4096 n (R % mm) :=
        spec.mpFrame 6144 6144 6144 4096 _ _ (by omega) (Or.inr (by omega)) ih.r1
      have hcc1 : Model.FastRepresents (mpMem 6144 6144 6144 (rrMem mpMem n mem i))
          5120 n (Limbs.radix * R % mm) :=
        spec.mpFrame 6144 6144 6144 5120 _ _ (by omega) (Or.inr (by omega)) ih.cc
      have hsel : Model.FastRepresents (mpMem 6144 6144 6144 (rrMem mpMem n mem i))
          (selOf n (5 - i)) n
          (if bitAt n (5 - i) = 0 then R % mm else Limbs.radix * R % mm) := by
        by_cases h0 : bitAt n (5 - i) = 0
        · rw [if_pos h0, selOf, h0]
          simpa using hr11
        · have h1 : bitAt n (5 - i) = 1 := by
            have := bitAt_le_one n (5 - i)
            omega
          rw [if_neg h0, selOf, h1]
          simpa using hcc1
      have hsellt : (if bitAt n (5 - i) = 0 then R % mm else Limbs.radix * R % mm)
          < mm := by
        by_cases h0 : bitAt n (5 - i) = 0
        · rw [if_pos h0]; exact Nat.mod_lt _ hm
        · rw [if_neg h0]; exact Nat.mod_lt _ hm
      show RrInv (rrStep mpMem n (5 - i) (rrMem mpMem n mem i)) n mm R
        (rrValue mm R n (i + 1))
      by_cases h0 : bitAt n (5 - i) = 0
      · rw [rrStep, if_pos h0, rrValue_succ, if_pos h0,
          montMul_by_one hm hcop (Model.montMul_lt hm _ _ _)]
        exact ⟨hmod1, hr11, hcc1, hsq⟩
      · have h1 : selOf n (5 - i) = 5120 := by
          have := bitAt_le_one n (5 - i); unfold selOf; omega
        rw [h1, if_neg h0] at hsel
        rw [if_neg h0] at hsellt
        rw [rrStep, if_neg h0, rrValue_succ, if_neg h0]
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact spec.mpFrame 6144 5120 6144 0 mm _ (by omega)
            (Or.inr (by omega)) hmod1
        · exact spec.mpFrame 6144 5120 6144 4096 _ _ (by omega)
            (Or.inr (by omega)) hr11
        · exact spec.mpFrame 6144 5120 6144 5120 _ _ (by omega)
            (Or.inr (by omega)) hcc1
        · exact spec.mpValue 6144 5120 6144 _ _ _ (by omega)
            (by omega) (by omega) hmod1 hmi1 hsq hsel
            (Model.montMul_lt hm _ _ _) hsellt

/-- **The `RR` chain postcondition, at the level of memory.**  After the six
iterations the `RR` block holds the Montgomery form of `radix ^ n`, which for
`R = radix ^ n mod m` is `R ^ 2 mod m`. -/
theorem rrMem_final {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hn32 : n ≤ 32) (hcop : Nat.Coprime R mm) (mem : ByteArray)
    (hminv : MachineState.readWord mem 9376 = UInt256.ofNat minv)
    (hinv : RrInv mem n mm R (R % mm)) :
    Model.FastRepresents (rrMem mpMem n mem 6) 6144 n (rrValue mm R n 6) ∧
      rrValue mm R n 6 ≡ Limbs.radix ^ n * R [MOD mm] :=
  ⟨(rrMem_inv spec hm hcop hn32 mem hminv hinv 6).rr, rrValue_final hm hcop hn32⟩

/-! ### Bridges for the base-chain limb store

`Fast.Correct` needs to know that the word iteration `j` stores into `ONE` is
base limb `pb - 1 - j`, and that writing it replaces the whole `ONE` block. -/

/-- Reading one 32-byte word out of a longer big-endian field. -/
theorem bytesToNatPadded_word (bs : ByteArray) (off w r : Nat) (hr : r + 32 ≤ w) :
    Precompile.bytesToNatPadded bs off w / 256 ^ r % 256 ^ 32 =
      Precompile.bytesToNatPadded bs (off + (w - r - 32)) 32 := by
  have h1 := Challenge.EvmProof.Bytes.bytesToNatPadded_add bs off (w - r) r
  rw [show w - r + r = w from by omega] at h1
  have t1 := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow bs (off + (w - r)) r
  have h1' : Precompile.bytesToNatPadded bs off w =
      256 ^ r * Precompile.bytesToNatPadded bs off (w - r) +
        Precompile.bytesToNatPadded bs (off + (w - r)) r := by rw [h1]; ring
  have hdiv : Precompile.bytesToNatPadded bs off w / 256 ^ r =
      Precompile.bytesToNatPadded bs off (w - r) := by
    rw [h1', Nat.mul_add_div (pow_pos (by norm_num) r), Nat.div_eq_of_lt t1,
      Nat.add_zero]
  have h2 := Challenge.EvmProof.Bytes.bytesToNatPadded_add bs off (w - r - 32) 32
  rw [show w - r - 32 + 32 = w - r from by omega] at h2
  have t2 := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow bs
    (off + (w - r - 32)) 32
  have h2' : Precompile.bytesToNatPadded bs off (w - r) =
      Precompile.bytesToNatPadded bs (off + (w - r - 32)) 32 +
        Precompile.bytesToNatPadded bs off (w - r - 32) * 256 ^ 32 := by rw [h2]; ring
  rw [hdiv, h2', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt t2]

/-- The word iteration `j` stores into `ONE` is base limb `pb - 1 - j`. -/
theorem baseLimbWord_value (input : ByteArray) (bsize pb j : Nat)
    (hjpb : j < pb) (hle : 32 * (pb - j) ≤ bsize) :
    (baseLimbWord input bsize pb j).toNat =
      Precompile.bytesToNatPadded input 96 bsize / Limbs.radix ^ (pb - 1 - j) %
        Limbs.radix := by
  rw [baseLimbWord, Challenge.EvmProof.Bytes.readWord_toNat,
    show 96 + (bsize - 32 * (pb - j)) =
      96 + (bsize - 32 * (pb - j - 1) - 32) from by omega,
    ← bytesToNatPadded_word input 96 bsize (32 * (pb - j - 1)) (by omega),
    Limbs.pow_radix (pb - 1 - j), Limbs.radix_eq,
    show 32 * (pb - 1 - j) = 32 * (pb - j - 1) from by omega]

/-- Writing the least significant limb of a block whose value is below the
radix replaces the whole value. -/
theorem write_low_limb {mem : ByteArray} {n one : Nat} (word : UInt256)
    (hn : 0 < n) (hrep : Model.FastRepresents mem 3072 n one)
    (hone : one < Limbs.radix) :
    Model.FastRepresents (storeWord mem (3040 + 32 * n) word) 3072 n word.toNat := by
  have h := Model.fastRepresents_write_limb (k := 0) (value' := word.toNat) word hrep hn
    (by
      rw [pow_zero, Nat.div_one, Nat.mod_eq_of_lt hone, Nat.mul_one, Nat.mul_one]
      omega)
  rw [show (3072 : Nat) + 32 * (n - 1 - 0) = 3040 + 32 * n from by omega] at h
  exact h


/-! ## The hand-over from `Fast.Setup`

`Fast.Setup` stops at pc 1911 — the `DOUBLE256` entry — with stack
`[R1, 1533] ++ OUTER`.  Two `DOUBLE256` calls with the two `MCOPY` blocks `r0`
(pc 1533) and `r1` (pc 1555) between and after them lead into the `RR` chain at
pc 1569.  `DOUBLE256` enters through the same kind of abstract contract as
`MONPRO` and `ADDMOD`; `Fast.Double.gasSteps_double256_addmod` supplies it. -/

/-- The `DOUBLE256` entry, pc 1911, stack `[px, ret] ++ OUTER`. -/
def dblCall (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 1911
           stack := UInt256.ofNat px :: ret :: outer n bsize esize msize
           memory := mem }

/-- The `R1B` entry, pc 2901, stack `[px, ret] ++ OUTER`.  Same calling
convention as `DOUBLE256`, which it dispatches to when the guard fails. -/
def r1Call (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2901
           stack := UInt256.ofNat px :: ret :: outer n bsize esize msize
           memory := mem }

/-- The `CCB` entry, pc 2863, stack `[px, ret] ++ OUTER`.  `CCB` has the same
calling convention as `DOUBLE256` and the same postcondition — the block at
`px` is multiplied by `radix` modulo `m` — but reaches it with one `ADDMOD`
and eight `MONPRO` calls instead of 256 `ADDMOD` calls. -/
def ccCall (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2863
           stack := UInt256.ofNat px :: ret :: outer n bsize esize msize
           memory := mem }

/-- `r0`, pc 1533. -/
def r0State (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 1533
           stack := outer n bsize esize msize
           memory := mem }

/-- `r1`, pc 1555. -/
def r1State (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 1555
           stack := outer n bsize esize msize
           memory := mem }

set_option linter.unusedSimpArgs false in
/-- `blk1138` (pc 1533..1554): `MCOPY(CC, R1, s32)` then `CCB(CC)`. -/
theorem run_r0 (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hact : 298 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1138
      (r0State s mem n bsize esize msize) =
      some (ccCall s (mcopyMem mem 5120 4096 (32 * n)) 5120 (UInt256.ofNat 1555)
        n bsize esize msize) := by
  have hmod : (32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 32 * n :=
    mod_word_self (Nat.lt_of_le_of_lt (show 32 * n ≤ 1024 by omega) (by norm_num))
  have hfix1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      9344 32) = s.activeWords :=
    activeWords_fix s 9344 32 (by omega) (by omega) hact
  have hfix2 : UInt256.ofNat (MachineState.activeWordsAfter
      (MachineState.activeWordsAfter s.activeWords.toNat 5120 (32 * n)) 4096
      (32 * n)) = s.activeWords :=
    activeWords_fix2 s 5120 (32 * n) 4096 (32 * n) (by omega) (by omega) (by omega)
      (by omega) hact
  have h2863 : (2863 : UInt256) = UInt256.ofNat 2863 := by decide
  have h2863Nat : (UInt256.ofNat 2863).toNat = 2863 := by decide
  simp (config := { maxSteps := 600000 }) [blk1138, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    r0State, ccCall, mcopyMem, outer, fastPC4, hcode, hrun, hs32, hmod, hfix1,
    hfix2, h2863, h2863Nat, jumpDest2863, State.activeWordsAfterUInt256,
    State.activeWordsAfterUInt256_2,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk1148` (pc 1555..1567): `MCOPY(RR, R1, s32)` and the `RR` counter. -/
theorem run_r1 (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hact : 298 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1148
      (r1State s mem n bsize esize msize) =
      some (rrHead s (mcopyMem mem 6144 4096 (32 * n)) n bsize esize msize 5) := by
  have hmod : (32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 32 * n :=
    mod_word_self (Nat.lt_of_le_of_lt (show 32 * n ≤ 1024 by omega) (by norm_num))
  have hfix1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      9344 32) = s.activeWords :=
    activeWords_fix s 9344 32 (by omega) (by omega) hact
  have hfix2 : UInt256.ofNat (MachineState.activeWordsAfter
      (MachineState.activeWordsAfter s.activeWords.toNat 6144 (32 * n)) 4096
      (32 * n)) = s.activeWords :=
    activeWords_fix2 s 6144 (32 * n) 4096 (32 * n) (by omega) (by omega) (by omega)
      (by omega) hact
  simp (config := { maxSteps := 600000 }) [blk1148, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    r1State, rrHead, mcopyMem, outer, hrun, hs32, hmod, hfix1, hfix2, fastPC4,
    State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_r0 (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hact : 298 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (r0State s mem n bsize esize msize)
      (ccCall s (mcopyMem mem 5120 4096 (32 * n)) 5120 (UInt256.ofNat 1555)
        n bsize esize msize) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1138 hcode hfork
      (run_r0 s mem n bsize esize msize hn hn32 hact hs32 hcode hrun) hrun hnp

def gasSteps_r1 (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hact : 298 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (r1State s mem n bsize esize msize)
      (rrHead s (mcopyMem mem 6144 4096 (32 * n)) n bsize esize msize 5) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1148 hcode hfork
      (run_r1 s mem n bsize esize msize hn hn32 hact hs32 hrun) hrun hnp

/-- The memory the `DOUBLE256` call, the `CCB` call and the two `MCOPY`s
leave. -/
def setupToRRMem (dblF ccF : Nat → ByteArray → ByteArray) (n : Nat)
    (mem : ByteArray) : ByteArray :=
  mcopyMem (ccF 5120 (mcopyMem (dblF 4096 mem) 5120 4096 (32 * n))) 6144 4096
    (32 * n)



/-! ### The base chain, at the level of memory -/

theorem storeWord_frame (mem : ByteArray) (addr ptr count value : Nat) (w : UInt256)
    (hdisj : addr + 32 ≤ ptr ∨ ptr + 32 * count ≤ addr)
    (hrep : Model.FastRepresents mem ptr count value) :
    Model.FastRepresents (storeWord mem addr w) ptr count value :=
  Model.fastRepresents_writeWord_disjoint mem addr ptr count value w.toNat hdisj hrep

theorem storeWord_readWord_disjoint (mem : ByteArray) (addr a : Nat) (w : UInt256)
    (hdisj : a + 32 ≤ addr ∨ addr + 32 ≤ a) :
    MachineState.readWord (storeWord mem addr w) a =
      MachineState.readWord mem a := by
  refine Challenge.EvmProof.Memory.readWord_writeBytes_disjoint mem _ a addr ?_
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  exact hdisj

theorem readWord_mcopyMem_disjoint (mem : ByteArray) (dst src sz a : Nat)
    (hdisj : a + 32 ≤ dst ∨ dst + sz ≤ a) :
    MachineState.readWord (mcopyMem mem dst src sz) a =
      MachineState.readWord mem a := by
  refine Challenge.EvmProof.Memory.readWord_writeBytes_disjoint mem _ a dst ?_
  rw [Challenge.EvmProof.Memory.readPadded_size]
  exact hdisj

/-- A store below `V_S32` preserves the configuration words. -/
theorem frame_storeWord {mem : ByteArray} {n bsize minv addr : Nat} (w : UInt256)
    (haddr : addr + 32 ≤ 9344) (hf : Frame mem n bsize minv) :
    Frame (storeWord mem addr w) n bsize minv where
  s32 := by
    rw [storeWord_readWord_disjoint mem addr 9344 w (Or.inr (by omega))]; exact hf.s32
  minvW := by
    rw [storeWord_readWord_disjoint mem addr 9376 w (Or.inr (by omega))]
    exact hf.minvW
  ml := by
    rw [storeWord_readWord_disjoint mem addr 9408 w (Or.inr (by omega))]; exact hf.ml
  tl := by
    rw [storeWord_readWord_disjoint mem addr 9440 w (Or.inr (by omega))]; exact hf.tl
  eoff := by
    rw [storeWord_readWord_disjoint mem addr 9472 w (Or.inr (by omega))]
    exact hf.eoff

/-- An `MCOPY` below `V_S32` preserves the configuration words. -/
theorem frame_mcopyMem {mem : ByteArray} {n bsize minv dst src sz : Nat}
    (hfit : dst + sz ≤ 9344) (hf : Frame mem n bsize minv) :
    Frame (mcopyMem mem dst src sz) n bsize minv where
  s32 := by
    rw [readWord_mcopyMem_disjoint mem dst src sz 9344 (Or.inr (by omega))]
    exact hf.s32
  minvW := by
    rw [readWord_mcopyMem_disjoint mem dst src sz 9376 (Or.inr (by omega))]
    exact hf.minvW
  ml := by
    rw [readWord_mcopyMem_disjoint mem dst src sz 9408 (Or.inr (by omega))]
    exact hf.ml
  tl := by
    rw [readWord_mcopyMem_disjoint mem dst src sz 9440 (Or.inr (by omega))]
    exact hf.tl
  eoff := by
    rw [readWord_mcopyMem_disjoint mem dst src sz 9472 (Or.inr (by omega))]
    exact hf.eoff

theorem blValue_lt {mm b pb : Nat} (hm : 0 < mm) (t : Nat) :
    blValue mm b pb t < mm := by
  cases t with
  | zero => exact Nat.mod_lt _ hm
  | succ t => exact Nat.mod_lt _ hm

/-- The most significant partial base limb is the top limb of the base. -/
theorem topLimbOf_value (input : ByteArray) (bsize : Nat) (hb0 : 1 ≤ bsize) :
    topLimbOf input bsize =
      Precompile.bytesToNatPadded input 96 bsize / Limbs.radix ^ (pbOf bsize - 1) := by
  have hw : topWidth bsize + (bsize - topWidth bsize) = bsize := by
    unfold topWidth pbOf; omega
  have hexp : bsize - topWidth bsize = 32 * (pbOf bsize - 1) := by
    unfold topWidth pbOf; omega
  have hpow : (256 : Nat) ^ (bsize - topWidth bsize) =
      Limbs.radix ^ (pbOf bsize - 1) := by
    rw [hexp, Limbs.pow_radix]
  have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add input 96 (topWidth bsize)
    (bsize - topWidth bsize)
  rw [hw] at hsplit
  have htail := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input
    (96 + topWidth bsize) (bsize - topWidth bsize)
  rw [hpow] at htail
  have hsplit' : Precompile.bytesToNatPadded input 96 bsize =
      Limbs.radix ^ (pbOf bsize - 1) * topLimbOf input bsize +
        Precompile.bytesToNatPadded input (96 + topWidth bsize)
          (bsize - topWidth bsize) := by
    rw [hsplit, topLimbOf, hpow]; ring
  rw [hsplit', Nat.mul_add_div (pow_pos Limbs.radix_pos _), Nat.div_eq_of_lt htail,
    Nat.add_zero]

/-- The blocks the Horner loop reads and writes: the modulus, `ACC`, `ONE`
(whose value always fits in one limb), `CC` and `RR`. -/
structure BlInv (mem : ByteArray) (n mm R rr acc : Nat) : Prop where
  modulus : Model.FastRepresents mem 0 n mm
  accBlock : Model.FastRepresents mem 1024 n acc
  oneBlock : ∃ one, one < Limbs.radix ∧ Model.FastRepresents mem 3072 n one
  ccBlock : Model.FastRepresents mem 5120 n (Limbs.radix * R % mm)
  rrBlock : Model.FastRepresents mem 6144 n rr

/-- The memory one Horner iteration produces. -/
def blStepMem (mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (input : ByteArray) (n bsize pb : Nat) (mem : ByteArray) (j : Nat) : ByteArray :=
  amMem 1024 3072 1024
    (storeWord (mpMem 1024 5120 1024 mem) (3040 + 32 * n)
      (baseLimbWord input bsize pb j))

theorem blMems_succ (mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (input : ByteArray) (n bsize pb : Nat) (mem : ByteArray) (t : Nat) :
    blMems mpMem amMem input n bsize pb mem (t + 1) =
      blStepMem mpMem amMem input n bsize pb
        (blMems mpMem amMem input n bsize pb mem t) (t + 1) := rfl

/-- One Horner iteration: `ACC := MonPro(ACC, CC)`, store base limb
`pb - 1 - j` into `ONE`, `ACC := AddMod(ACC, ONE)`. -/
theorem blStep_inv {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R rr minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hcop : Nat.Coprime R mm)
    (hradix : Limbs.radix ≤ mm) (input : ByteArray) (bsize pb j : Nat)
    (hjpb : j < pb) (hle : 32 * (pb - j) ≤ bsize)
    (mem : ByteArray) (acc : Nat) (hacc : acc < mm)
    (hminv : MachineState.readWord mem 9376 = UInt256.ofNat minv)
    (hinv : BlInv mem n mm R rr acc) :
    BlInv (blStepMem mpMem amMem input n bsize pb mem j) n mm R rr
      ((acc * Limbs.radix % mm +
        Precompile.bytesToNatPadded input 96 bsize / Limbs.radix ^ (pb - 1 - j) %
          Limbs.radix) % mm) := by
  obtain ⟨one, honelt, honerep⟩ := hinv.oneBlock
  -- the Montgomery multiply by `CC`
  have hmul := spec.mpValue 1024 5120 1024 mem acc (Limbs.radix * R % mm)
    (by omega) (by omega) (by omega) hinv.modulus hminv hinv.accBlock hinv.ccBlock
    hacc (Nat.mod_lt _ hm)
  rw [Model.montMul_const_form hm hcop (Nat.mod_modEq (Limbs.radix * R) mm) acc] at hmul
  have hmod1 := spec.mpFrame 1024 5120 1024 0 mm mem (by omega) (Or.inr (by omega))
    hinv.modulus
  have hone1 := spec.mpFrame 1024 5120 1024 3072 one mem (by omega)
    (Or.inl (by omega)) honerep
  have hcc1 := spec.mpFrame 1024 5120 1024 5120 (Limbs.radix * R % mm) mem (by omega)
    (Or.inl (by omega)) hinv.ccBlock
  have hrr1 := spec.mpFrame 1024 5120 1024 6144 rr mem (by omega) (Or.inl (by omega))
    hinv.rrBlock
  -- the limb store into `ONE`
  have hstore := write_low_limb (baseLimbWord input bsize pb j) (by omega) hone1 honelt
  have hmod2 := storeWord_frame (mpMem 1024 5120 1024 mem) (3040 + 32 * n) 0 n mm
    (baseLimbWord input bsize pb j) (Or.inr (by omega)) hmod1
  have hacc2 := storeWord_frame (mpMem 1024 5120 1024 mem) (3040 + 32 * n) 1024 n
    (acc * Limbs.radix % mm) (baseLimbWord input bsize pb j) (Or.inr (by omega)) hmul
  have hcc2 := storeWord_frame (mpMem 1024 5120 1024 mem) (3040 + 32 * n) 5120 n
    (Limbs.radix * R % mm) (baseLimbWord input bsize pb j) (Or.inl (by omega)) hcc1
  have hrr2 := storeWord_frame (mpMem 1024 5120 1024 mem) (3040 + 32 * n) 6144 n rr
    (baseLimbWord input bsize pb j) (Or.inl (by omega)) hrr1
  -- the modular addition
  have hlimb := baseLimbWord_value input bsize pb j hjpb hle
  have hlimblt : (baseLimbWord input bsize pb j).toNat < Limbs.radix :=
    (baseLimbWord input bsize pb j).val.isLt
  have hsum : acc * Limbs.radix % mm + (baseLimbWord input bsize pb j).toNat <
      2 * mm := by
    have h1 : acc * Limbs.radix % mm < mm := Nat.mod_lt _ hm
    omega
  have hadd := spec.amValue 1024 3072 1024
    (storeWord (mpMem 1024 5120 1024 mem) (3040 + 32 * n)
      (baseLimbWord input bsize pb j)) (acc * Limbs.radix % mm)
    (baseLimbWord input bsize pb j).toNat (by omega) (by omega) (by omega)
    hmod2 hacc2 hstore hsum
  rw [hlimb] at hadd
  refine ⟨?_, hadd, ⟨(baseLimbWord input bsize pb j).toNat, hlimblt, ?_⟩, ?_, ?_⟩
  · exact spec.amFrame 1024 3072 1024 0 mm _ (by omega) (Or.inr (by omega)) hmod2
  · exact spec.amFrame 1024 3072 1024 3072 _ _ (by omega) (Or.inl (by omega))
      (hlimb ▸ hstore)
  · exact spec.amFrame 1024 3072 1024 5120 (Limbs.radix * R % mm) _ (by omega)
      (Or.inl (by omega)) hcc2
  · exact spec.amFrame 1024 3072 1024 6144 rr _ (by omega) (Or.inl (by omega)) hrr2

/-- `V_MINV` survives the Horner loop. -/
theorem readWord_blMems (mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (hmp : ∀ (pa pb : Nat) (mem' : ByteArray),
      MachineState.readWord (mpMem pa pb 1024 mem') 9376 =
        MachineState.readWord mem' 9376)
    (ham : ∀ (pa pb : Nat) (mem' : ByteArray),
      MachineState.readWord (amMem pa pb 1024 mem') 9376 =
        MachineState.readWord mem' 9376)
    (input : ByteArray) (n bsize pb : Nat) (hn32 : n ≤ 32) (mem : ByteArray)
    (t : Nat) :
    MachineState.readWord (blMems mpMem amMem input n bsize pb mem t) 9376 =
      MachineState.readWord mem 9376 := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [blMems_succ, blStepMem, ham 1024 3072 _,
        storeWord_readWord_disjoint _ (3040 + 32 * n) 9376 _ (Or.inr (by omega)),
        hmp 1024 5120 _, ih]

/-- **The Horner loop, at the level of memory.** -/
theorem blMems_inv {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R rr minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hcop : Nat.Coprime R mm)
    (hradix : Limbs.radix ≤ mm) (input : ByteArray) (bsize : Nat)
    (hb0 : 1 ≤ bsize) (mem : ByteArray)
    (hminv : MachineState.readWord mem 9376 = UInt256.ofNat minv)
    (hinv : BlInv mem n mm R rr
      (blValue mm (Precompile.bytesToNatPadded input 96 bsize) (pbOf bsize) 0)) :
    ∀ t, t < pbOf bsize →
      BlInv (blMems mpMem amMem input n bsize (pbOf bsize) mem t) n mm R rr
        (blValue mm (Precompile.bytesToNatPadded input 96 bsize) (pbOf bsize) t) := by
  intro t
  induction t with
  | zero => intro _; exact hinv
  | succ t ih =>
      intro ht
      have hstep := blStep_inv spec hm hn hn32 hcop hradix input bsize (pbOf bsize)
        (t + 1) ht (by unfold pbOf; omega)
        (blMems mpMem amMem input n bsize (pbOf bsize) mem t)
        (blValue mm (Precompile.bytesToNatPadded input 96 bsize) (pbOf bsize) t)
        (blValue_lt hm t)
        ((readWord_blMems mpMem amMem
          (fun pa pb m => spec.mpMinv pa pb 1024 m (by omega))
          (fun pa pb m => spec.amMinv pa pb 1024 m (by omega)) input n bsize
          (pbOf bsize) hn32 mem t).trans hminv)
        (ih (by omega))
      rw [blMems_succ, blValue_succ]
      exact hstep

/-- **The base-chain postcondition, at the level of memory.**  After `pb - 1`
Horner iterations the `ACC` block holds `b mod m`. -/
theorem blMem_final {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R rr minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hcop : Nat.Coprime R mm)
    (hradix : Limbs.radix ≤ mm) (input : ByteArray) (bsize : Nat)
    (hb0 : 1 ≤ bsize) (mem : ByteArray)
    (hminv : MachineState.readWord mem 9376 = UInt256.ofNat minv)
    (hinv : BlInv mem n mm R rr
      (blValue mm (Precompile.bytesToNatPadded input 96 bsize) (pbOf bsize) 0)) :
    Model.FastRepresents
      (blMems mpMem amMem input n bsize (pbOf bsize) mem (pbOf bsize - 1)) 1024 n
      (Precompile.bytesToNatPadded input 96 bsize % mm) := by
  have h := (blMems_inv spec hm hn hn32 hcop hradix input bsize hb0 mem hminv hinv
    (pbOf bsize - 1) (by unfold pbOf; omega)).accBlock
  rwa [blValue_final mm (Precompile.bytesToNatPadded input 96 bsize) (pbOf bsize)
    (by unfold pbOf; omega)] at h

/-- **`BASE := MonPro(ACC, RR)`.**  With `RR` holding `R ^ 2 mod m` this leaves
`b * R mod m` in the `BASE` block. -/
theorem blMem_base {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R rr b minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hn32 : n ≤ 32) (hcop : Nat.Coprime R mm) (hrr : rr ≡ R * R [MOD mm])
    (hrrlt : rr < mm) (mem : ByteArray)
    (hminv : MachineState.readWord mem 9376 = UInt256.ofNat minv)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hacc : Model.FastRepresents mem 1024 n (b % mm))
    (hrrb : Model.FastRepresents mem 6144 n rr) :
    Model.FastRepresents (mpMem 1024 6144 2048 mem) 2048 n (b * R % mm) := by
  have h := spec.mpValue 1024 6144 2048 mem (b % mm) rr (by omega) (by omega)
    (by omega) hmod hminv hacc hrrb (Nat.mod_lt _ hm) hrrlt
  rwa [Model.montMul_const_form hm hcop hrr (b % mm),
    show b % mm * R % mm = b * R % mm from ((Nat.mod_modEq b mm).mul_right R)] at h


/-! ### The exponent loop, at the level of memory -/

/-- The bit the loop consumes at global step `t`: bit `7 - t % 8` of exponent
byte `t / 8`. -/
def expBits (input : ByteArray) (bsize : Nat) (t : Nat) : Nat :=
  bitAt (expByte input bsize (t / 8)) (7 - t % 8)

theorem expBits_eq (input : ByteArray) (bsize i j : Nat) (hj : j < 8) :
    expBits input bsize (8 * i + j) = bitAt (expByte input bsize i) (7 - j) := by
  unfold expBits
  rw [show (8 * i + j) / 8 = i from by omega, show (8 * i + j) % 8 = j from by omega]

theorem expAcc_lt {mm R bM : Nat} (hm : 0 < mm) (bits : Nat → Nat) (t : Nat) :
    expAcc mm R bM bits t < mm := by
  cases t with
  | zero => exact Nat.mod_lt _ hm
  | succ t =>
      rw [expAcc_succ]
      split
      · exact Model.montMul_lt hm _ _ _
      · exact Model.montMul_lt hm _ _ _

/-- The blocks the exponent loop reads and writes: the modulus, `ACC`, `BASE`
and `ONE` (untouched, and still one limb wide). -/
structure EbInv (mem : ByteArray) (n mm bM acc : Nat) : Prop where
  modulus : Model.FastRepresents mem 0 n mm
  accBlock : Model.FastRepresents mem 1024 n acc
  baseBlock : Model.FastRepresents mem 2048 n bM
  oneBlock : ∃ one, one < Limbs.radix ∧ Model.FastRepresents mem 3072 n one

/-- One exponent bit: square `ACC`, and multiply by `BASE` when the bit is
set. -/
theorem bitStep_inv {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hn32 : n ≤ 32) (mem : ByteArray) (bM acc bit : Nat) (hbit : bit ≤ 1)
    (hbM : bM < mm) (hacc : acc < mm)
    (hminv : MachineState.readWord mem 9376 = UInt256.ofNat minv)
    (hinv : EbInv mem n mm bM acc) :
    EbInv (bitStep mpMem mem bit) n mm bM
      (if bit = 0 then Model.montMul mm R acc acc
        else Model.montMul mm R (Model.montMul mm R acc acc) bM) := by
  obtain ⟨one, honelt, honerep⟩ := hinv.oneBlock
  have hsq := spec.mpValue 1024 1024 1024 mem acc acc (by omega) (by omega)
    (by omega) hinv.modulus hminv hinv.accBlock hinv.accBlock hacc hacc
  have hmod1 := spec.mpFrame 1024 1024 1024 0 mm mem (by omega) (Or.inr (by omega))
    hinv.modulus
  have hbase1 := spec.mpFrame 1024 1024 1024 2048 bM mem (by omega)
    (Or.inl (by omega)) hinv.baseBlock
  have hone1 := spec.mpFrame 1024 1024 1024 3072 one mem (by omega)
    (Or.inl (by omega)) honerep
  rcases Nat.eq_zero_or_pos bit with h0 | hpos
  · subst h0
    refine ⟨hmod1, ?_, hbase1, ⟨one, honelt, hone1⟩⟩
    show Model.FastRepresents (mpMem 1024 1024 1024 mem) 1024 n
      (Model.montMul mm R acc acc)
    exact hsq
  · have h1 : bit = 1 := by omega
    subst h1
    have hmul := spec.mpValue 1024 2048 1024 (mpMem 1024 1024 1024 mem)
      (Model.montMul mm R acc acc) bM (by omega) (by omega) (by omega) hmod1
      ((spec.mpMinv 1024 1024 1024 mem (by omega)).trans hminv) hsq hbase1
      (Model.montMul_lt hm _ _ _) hbM
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact spec.mpFrame 1024 2048 1024 0 mm _ (by omega) (Or.inr (by omega)) hmod1
    · show Model.FastRepresents (mpMem 1024 2048 1024 (mpMem 1024 1024 1024 mem))
        1024 n (Model.montMul mm R (Model.montMul mm R acc acc) bM)
      exact hmul
    · exact spec.mpFrame 1024 2048 1024 2048 bM _ (by omega) (Or.inl (by omega))
        hbase1
    · exact ⟨one, honelt, spec.mpFrame 1024 2048 1024 3072 one _ (by omega)
        (Or.inl (by omega)) hone1⟩

/-- The eight bits of one exponent byte. -/
theorem bitMems_inv {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hn32 : n ≤ 32) (bM : Nat) (hbM : bM < mm) (w : Nat) (bits : Nat → Nat)
    (t0 : Nat) (hbits : ∀ j, j < 8 → bits (t0 + j) = bitAt w (7 - j))
    (mem : ByteArray)
    (hminv : MachineState.readWord mem 9376 = UInt256.ofNat minv)
    (hinv : EbInv mem n mm bM (expAcc mm R bM bits t0)) :
    ∀ j, j ≤ 8 →
      EbInv (bitMems mpMem w mem j) n mm bM (expAcc mm R bM bits (t0 + j)) := by
  intro j
  induction j with
  | zero => intro _; exact hinv
  | succ j ih =>
      intro hj
      have hstep := bitStep_inv spec hm hn32 (bitMems mpMem w mem j) bM
        (expAcc mm R bM bits (t0 + j)) (bitAt w (7 - j)) (bitAt_le_one w (7 - j)) hbM
        (expAcc_lt hm bits (t0 + j))
        ((readWord_bitMems mpMem 9376 (fun pa pb m => spec.mpMinv pa pb 1024 m (by omega)) w
          mem j).trans hminv)
        (ih (by omega))
      rw [show t0 + (j + 1) = t0 + j + 1 from rfl, expAcc_succ, hbits j (by omega)]
      exact hstep

theorem bitAt_zero_of_lt {w r j : Nat} (hw : w < 2 ^ (r + 1)) (hj : r < j) :
    bitAt w j = 0 := by
  have hle : (2 : Nat) ^ (r + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold bitAt
  rw [Nat.div_eq_of_lt (by omega)]

theorem montMul_mont_one {mm R : Nat} (hm : 0 < mm) (hcop : Nat.Coprime R mm) :
    Model.montMul mm R (R % mm) (R % mm) = R % mm :=
  Model.montMul_eq_of_modEq hm hcop
    (Nat.ModEq.mul_left (R % mm) (Nat.mod_modEq R mm).symm) (Nat.mod_lt _ hm)

/-- Squaring over leading zero bits leaves the accumulator at `Mont 1`. -/
theorem expAcc_of_zeros {mm R bM : Nat} (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    (bits : Nat → Nat) (k : Nat) (hz : ∀ j, j < k → bits j = 0) :
    expAcc mm R bM bits k = R % mm := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [expAcc_succ, hz k (by omega), if_pos rfl,
        ih (fun j hj => hz j (by omega))]
      exact montMul_mont_one hm hcop

theorem bitMemsFrom_inv {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hn32 : n ≤ 32) (bM : Nat) (hbM : bM < mm) (w : Nat) (bits : Nat → Nat)
    (t0 j0 : Nat)
    (hbits : ∀ k, k < 8 - j0 → bits (t0 + j0 + k) = bitAt w (7 - (j0 + k)))
    (mem : ByteArray)
    (hminv : MachineState.readWord mem 9376 = UInt256.ofNat minv)
    (hinv : EbInv mem n mm bM (expAcc mm R bM bits (t0 + j0))) :
    ∀ k, k ≤ 8 - j0 →
      EbInv (bitMemsFrom mpMem w mem j0 k) n mm bM
        (expAcc mm R bM bits (t0 + j0 + k)) := by
  intro k
  induction k with
  | zero => intro _; exact hinv
  | succ k ih =>
      intro hk
      have hstep := bitStep_inv spec hm hn32 (bitMemsFrom mpMem w mem j0 k) bM
        (expAcc mm R bM bits (t0 + j0 + k)) (bitAt w (7 - (j0 + k)))
        (bitAt_le_one w (7 - (j0 + k))) hbM (expAcc_lt hm bits (t0 + j0 + k))
        ((readWord_bitMemsFrom mpMem 9376
          (fun pa pb m => spec.mpMinv pa pb 1024 m (by omega)) w mem j0 k).trans hminv)
        (ih (by omega))
      rw [show t0 + j0 + (k + 1) = t0 + j0 + k + 1 from rfl, expAcc_succ,
        hbits k (by omega)]
      exact hstep

/-- `lzMask` is the power of two the bit loop starts from. -/
theorem lzMask_eq (input : ByteArray) (bsize i : Nat) :
    lzMask input bsize i = 2 ^ (7 - lzSkip input bsize i) := by
  unfold lzMask lzSkip
  split
  · obtain ⟨h1, h2, _⟩ := Lz.topBit_spec (expByte input bsize i)
      ((YulSemantics.EVM.byteFrom input.toList (96 + bsize + i)).toNat_lt)
    rw [h1, show 7 - (7 - Lz.topExp (expByte input bsize i))
      = Lz.topExp (expByte input bsize i) from by omega]
  · norm_num

/-- The bits the loop skips are leading zeros of the exponent, so the
accumulator it starts from is the one the unskipped loop would have had. -/
theorem ebInv_shift {n mm R bM : Nat} (hm : 0 < mm)
    (hcop : Nat.Coprime R mm) (input : ByteArray) (bsize i : Nat)
    (mem : ByteArray)
    (hinv : EbInv mem n mm bM (expAcc mm R bM (expBits input bsize) (8 * i))) :
    EbInv mem n mm bM
      (expAcc mm R bM (expBits input bsize) (8 * i + lzSkip input bsize i)) := by
  by_cases h0 : i = 0
  · subst h0
    have hz : ∀ j, j < lzSkip input bsize 0 → expBits input bsize j = 0 := by
      intro j hj
      obtain ⟨_, hle7, hwlt⟩ := Lz.topBit_spec (expByte input bsize 0)
        ((YulSemantics.EVM.byteFrom input.toList (96 + bsize + 0)).toNat_lt)
      have hjs : j < 7 - Lz.topExp (expByte input bsize 0) := by
        simpa [lzSkip] using hj
      have hlt : j < 8 := by omega
      have heq := expBits_eq input bsize 0 j hlt
      rw [show 8 * 0 + j = j from by ring] at heq
      rw [heq]
      exact bitAt_zero_of_lt hwlt (by omega)
    have he : expAcc mm R bM (expBits input bsize)
        (8 * 0 + lzSkip input bsize 0) =
        expAcc mm R bM (expBits input bsize) 0 := by
      rw [show 8 * 0 + lzSkip input bsize 0 = lzSkip input bsize 0 from by ring,
        expAcc_of_zeros hm hcop _ _ hz]
      rfl
    rw [he]
    exact hinv
  · have hz0 : lzSkip input bsize i = 0 := by simp only [lzSkip, if_neg h0]
    rw [hz0, Nat.add_zero]
    exact hinv

/-- **The exponent loop, at the level of memory.** -/
theorem ebMems_inv {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hcop : Nat.Coprime R mm)
    (hn32 : n ≤ 32) (bM : Nat) (hbM : bM < mm) (input : ByteArray) (bsize : Nat)
    (mem : ByteArray)
    (hminv : MachineState.readWord mem 9376 = UInt256.ofNat minv)
    (hinv : EbInv mem n mm bM (expAcc mm R bM (expBits input bsize) 0)) :
    ∀ i, EbInv (ebMems mpMem input bsize mem i) n mm bM
      (expAcc mm R bM (expBits input bsize) (8 * i)) := by
  intro i
  induction i with
  | zero => exact hinv
  | succ i ih =>
      have hj0 : lzSkip input bsize i ≤ 7 := lzSkip_le input bsize i
      have hstart := ebInv_shift (n := n) (bM := bM) hm hcop input bsize i
        (ebMems mpMem input bsize mem i) ih
      have h := bitMemsFrom_inv spec hm hn32 bM hbM (expByte input bsize i)
        (expBits input bsize) (8 * i) (lzSkip input bsize i)
        (fun k hk => by
          have := expBits_eq input bsize i (lzSkip input bsize i + k) (by omega)
          rwa [show 8 * i + (lzSkip input bsize i + k)
            = 8 * i + lzSkip input bsize i + k from by ring] at this)
        (ebMems mpMem input bsize mem i)
        ((readWord_ebMems mpMem 9376 (fun pa pb m => spec.mpMinv pa pb 1024 m (by omega)) input
          bsize mem i).trans hminv)
        hstart (8 - lzSkip input bsize i) le_rfl
      rw [show 8 * (i + 1)
        = 8 * i + lzSkip input bsize i + (8 - lzSkip input bsize i) from by omega]
      exact h

/-- **The exponent-loop postcondition, at the level of memory.**  After the
`8 * esize` bits, `MSTORE ONE 1` and the closing `MonPro(ACC, ONE)`, the `ACC`
block holds the precompile's answer. -/
theorem ebMem_final {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R bM b e minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hcop : Nat.Coprime R mm)
    (hradix : Limbs.radix ≤ mm) (hbM : bM < mm) (hbMform : bM ≡ b * R [MOD mm])
    (input : ByteArray) (bsize esize : Nat)
    (he : e = Precompile.bytesToNatPadded input (96 + bsize) esize)
    (mem : ByteArray)
    (hminv : MachineState.readWord mem 9376 = UInt256.ofNat minv)
    (hinv : EbInv mem n mm bM (expAcc mm R bM (expBits input bsize) 0)) :
    Model.FastRepresents
      (mpMem 1024 3072 1024
        (storeWord (ebMems mpMem input bsize mem esize) (3040 + 32 * n)
          (UInt256.ofNat 1))) 1024 n (Precompile.modPow b e mm) := by
  subst he
  have hmm1 : 1 < mm := lt_of_lt_of_le Limbs.radix_gt_one hradix
  have hloop := ebMems_inv spec hm hcop hn32 bM hbM input bsize mem hminv hinv esize
  have hmi : MachineState.readWord
      (storeWord (ebMems mpMem input bsize mem esize) (3040 + 32 * n)
        (UInt256.ofNat 1)) 9376 = UInt256.ofNat minv := by
    rw [storeWord_readWord_disjoint _ (3040 + 32 * n) 9376 _ (Or.inr (by omega))]
    exact (readWord_ebMems mpMem 9376 (fun pa pb m => spec.mpMinv pa pb 1024 m (by omega)) input
      bsize mem esize).trans hminv
  obtain ⟨one, honelt, honerep⟩ := hloop.oneBlock
  have hone := write_low_limb (UInt256.ofNat 1) (by omega) honerep honelt
  rw [show (UInt256.ofNat 1).toNat = 1 from by decide] at hone
  have hmod := storeWord_frame (ebMems mpMem input bsize mem esize) (3040 + 32 * n)
    0 n mm (UInt256.ofNat 1) (Or.inr (by omega)) hloop.modulus
  have hacc := storeWord_frame (ebMems mpMem input bsize mem esize) (3040 + 32 * n)
    1024 n (expAcc mm R bM (expBits input bsize) (8 * esize)) (UInt256.ofNat 1)
    (Or.inr (by omega)) hloop.accBlock
  have hout := spec.mpValue 1024 3072 1024
    (storeWord (ebMems mpMem input bsize mem esize) (3040 + 32 * n)
      (UInt256.ofNat 1))
    (expAcc mm R bM (expBits input bsize) (8 * esize)) 1 (by omega) (by omega)
    (by omega) hmod hmi hacc hone (expAcc_lt hm _ _) hmm1
  have helt : Precompile.bytesToNatPadded input (96 + bsize) esize <
      2 ^ (8 * esize) := by
    have h := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input (96 + bsize) esize
    rwa [show (256 : Nat) ^ esize = 2 ^ (8 * esize) from by
      rw [show (256 : Nat) = 2 ^ 8 from by norm_num, ← Nat.pow_mul]] at h
  have hbit : ∀ t, t < 8 * esize →
      expBits input bsize t =
        bitAt (Precompile.bytesToNatPadded input (96 + bsize) esize)
          (8 * esize - t - 1) := by
    intro t ht
    have hi : t / 8 < esize := by omega
    have h := bitAt_expByte input bsize esize (t / 8) (7 - t % 8) hi (by omega)
    rw [expBits, h, show 8 * (esize - 1 - t / 8) + (7 - t % 8) = 8 * esize - t - 1
      from by omega]
  rwa [expAcc_out hm hcop hbMform (expBits input bsize)
    (fun t => bitAt_le_one _ _) helt hbit] at hout

/-! ### The shape `Fast.Correct.FastPath.handled` consumes -/

theorem returnedState_isDone (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) (hstack : s.callStack = []) :
    (returnedState s mem n bsize esize msize).isDone = true := by
  simp [State.isDone, State.isHalted, State.isRunning, returnedState, hstack]

/-- **The halted state's result is the specification.**  Together with
`returnedState_isDone` and the chain traces this is exactly the
`∃ final, GasSteps … ∧ final.isDone = true ∧ final.toResult = .returned (spec input)`
that `Fast.Correct.FastPath.handled` asks for. -/
theorem returnedState_toResult (s : State) (mem input : ByteArray)
    (n bsize esize msize result : Nat) (hn : 2 ≤ n) (hm : msize ≤ 32 * n)
    (hmpos : 0 < msize)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hrep : Model.FastRepresents mem 1024 n result)
    (hres : result = Precompile.modPow
      (Precompile.bytesToNatPadded input 96 bsize)
      (Precompile.bytesToNatPadded input (96 + bsize) esize)
      (Precompile.bytesToNatPadded input (96 + bsize + esize) msize)) :
    (returnedState s mem n bsize esize msize).toResult =
      .returned (Challenge.Modexp.spec input) := by
  rw [State.toResult_returned _ (by rfl),
    returned_eq_spec s mem input n bsize esize msize result hn hm hmpos hbsize hesize
      hmsz hrep hres]



/-! ### The shape `Fast.Correct.FastPath.handled` wants

`Challenge.EvmProof.GasSteps` is `Type`, not `Prop`, so the literal
`∃ final : State, GasSteps … final ∧ …` does not elaborate: `And` needs both
sides in `Prop`.  Wrapping the trace in `Nonempty` fixes that, and
`Classical.choice` recovers the trace on the other side.

This module deliberately does *not* import `Fast.Setup`: that import drags the
whole reference-proof closure (`Bytecode.Word`, `BigExponent`, `BigMul`, …)
into this file's dependency graph.  The final assembly therefore belongs in
`Fast.Correct`, which imports everything already; `handled_of_trace` is the
one-liner it needs. -/

/-- **The `handled` obligation, from a trace and the value of the `ACC` block.**
`entry` is the state the entry hop produces (`Main.trampolineState input 1314`),
`s` the carrier of the fast-path states (`initialState submissionBytecode input 0`,
whose `callStack` is `[]` by `rfl`). -/
theorem handled_of_trace (input : ByteArray) (entry s : State) (mem : ByteArray)
    (n bsize esize msize result : Nat)
    (hstack : s.callStack = [])
    (htrace : Challenge.EvmProof.GasSteps entry
      (returnedState s mem n bsize esize msize))
    (hn : 2 ≤ n) (hmsz32 : msize ≤ 32 * n) (hmpos : 0 < msize)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hrep : Model.FastRepresents mem 1024 n result)
    (hres : result = Precompile.modPow
      (Precompile.bytesToNatPadded input 96 bsize)
      (Precompile.bytesToNatPadded input (96 + bsize) esize)
      (Precompile.bytesToNatPadded input (96 + bsize + esize) msize)) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps entry final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) :=
  ⟨returnedState s mem n bsize esize msize, ⟨htrace⟩,
    returnedState_isDone s mem n bsize esize msize hstack,
    returnedState_toResult s mem input n bsize esize msize result hn hmsz32 hmpos
      hbsize hesize hmsz hrep hres⟩


#print axioms blMem_final
#print axioms blMem_base
#print axioms ebMem_final
#print axioms rrMem_final
#print axioms returnedState_toResult
#print axioms handled_of_trace

/-! ## The gas traces of the three chains

These sit at the end of the module because each `iterateBounded` body needs the
value invariant at its own index, which the `*_inv` theorems above supply. -/

theorem jumpD (pc : Nat) (hpc : (UInt256.ofNat pc).toNat = pc)
    (hj : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode pc = true) :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat pc).toNat = true := by
  rw [hpc]; exact hj

theorem jumpD1586 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 1586).toNat = true := jumpD 1586 (by decide) jumpDest1586

theorem jumpD1615 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 1615).toNat = true := jumpD 1615 (by decide) jumpDest1615

theorem jumpD1693 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 1693).toNat = true := jumpD 1693 (by decide) jumpDest1693

theorem jumpD1728 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 1728).toNat = true := jumpD 1728 (by decide) jumpDest1728

theorem jumpD1755 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 1755).toNat = true := jumpD 1755 (by decide) jumpDest1755

theorem jumpD1806 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 1806).toNat = true := jumpD 1806 (by decide) jumpDest1806

theorem jumpD1831 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 1831).toNat = true := jumpD 1831 (by decide) jumpDest1831

theorem jumpD1533 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 1533).toNat = true := jumpD 1533 (by decide) jumpDest1533

theorem jumpD1555 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 1555).toNat = true := jumpD 1555 (by decide) jumpDest1555

theorem jumpD1876 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 1876).toNat = true := jumpD 1876 (by decide) jumpDest1876

/-- The configuration words survive the `RR` chain. -/
theorem rrMem_frame {s : State} {n bsize mm minv : Nat}
    (sub : Subroutines s n bsize mm minv) (mem : ByteArray)
    (hf : Frame mem n bsize minv) :
    ∀ i, Frame (rrMem sub.mpMem n mem i) n bsize minv := by
  intro i
  induction i with
  | zero => exact hf
  | succ i ih =>
      show Frame (rrStep sub.mpMem n (5 - i) (rrMem sub.mpMem n mem i)) n bsize minv
      unfold rrStep
      split
      · exact sub.mpFrame 6144 6144 6144 _ (by omega) ih
      · exact sub.mpFrame 6144 5120 6144 _ (by omega)
          (sub.mpFrame 6144 6144 6144 _ (by omega) ih)

set_option linter.unusedSimpArgs false in
/-- One iteration of the `RR` chain with a nonzero counter. -/
def gasSteps_rrBody (s : State) {n bsize mm minv R : Nat}
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm R minv)
    (mem : ByteArray) (esize msize k k' v : Nat)
    (hm : 0 < mm) (hn : n ≤ 32) (hk : k ≤ 5) (hk0 : k ≠ 0) (hkk : k = k' + 1)
    (hvlt : v < mm) (hframe : Frame mem n bsize minv) (hinv : RrInv mem n mm R v)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (rrHead s mem n bsize esize msize k)
      (rrHead s (rrStep sub.mpMem n k mem) n bsize esize msize k') := by
  have hbit := bitAt_le_one n k
  have hselhi : selOf n k ≤ 5120 := by unfold selOf; omega
  have hsello : 4096 ≤ selOf n k := by unfold selOf; omega
  have hsq : Model.FastRepresents (sub.mpMem 6144 6144 6144 mem) 6144 n
      (Model.montMul mm R v v) :=
    spec.mpValue 6144 6144 6144 mem v v (by omega) (by omega) (by omega)
      hinv.modulus hframe.minvW hinv.rr hinv.rr hvlt hvlt
  have hmod1 := spec.mpFrame 6144 6144 6144 0 mm mem (by omega) (Or.inr (by omega))
    hinv.modulus
  have hr11 := spec.mpFrame 6144 6144 6144 4096 (R % mm) mem (by omega)
    (Or.inr (by omega)) hinv.r1
  have hcc1 := spec.mpFrame 6144 6144 6144 5120 (Limbs.radix * R % mm) mem (by omega)
    (Or.inr (by omega)) hinv.cc
  have hframe1 : Frame (sub.mpMem 6144 6144 6144 mem) n bsize minv :=
    sub.mpFrame 6144 6144 6144 mem (by omega) hframe
  have hsel : Model.FastRepresents (sub.mpMem 6144 6144 6144 mem) (selOf n k) n
      (if bitAt n k = 0 then R % mm else Limbs.radix * R % mm) := by
    by_cases h0 : bitAt n k = 0
    · rw [if_pos h0, selOf, h0]; simpa using hr11
    · have h1 : bitAt n k = 1 := by omega
      rw [if_neg h0, selOf, h1]; simpa using hcc1
  have hmid : Challenge.EvmProof.GasSteps (rrHead s mem n bsize esize msize k)
      (rrSel s (sub.mpMem 6144 6144 6144 mem) n bsize esize msize k) :=
    ((gasSteps_rrHead s mem n bsize esize msize k hcode hfork hrun hnp).trans
      (sub.monpro 6144 6144 6144 (UInt256.ofNat 1586)
        (UInt256.ofNat k :: outer n bsize esize msize) mem v v (by simp)
        (by omega) (by omega) (by omega) (by omega) (by omega) jumpD1586 hframe
        hinv.modulus hinv.rr hinv.rr hvlt)).trans
      (gasSteps_rrMid s (sub.mpMem 6144 6144 6144 mem) n bsize esize msize k hn hk
        hcode hfork hrun hnp)
  have hsel2 : Challenge.EvmProof.GasSteps
      (rrSel s (sub.mpMem 6144 6144 6144 mem) n bsize esize msize k)
      (rrPost s (rrStep sub.mpMem n k mem) n bsize esize msize k) := by
    by_cases h0 : bitAt n k = 0
    · exact Challenge.EvmProof.GasSteps.cast
        ((gasSteps_rrSelSkip s (sub.mpMem 6144 6144 6144 mem) n bsize esize msize k h0
            hcode hfork hrun hnp).trans
          (gasSteps_rrSkipSel s (sub.mpMem 6144 6144 6144 mem) n bsize esize msize k
            hcode hfork hrun hnp))
        rfl (by simp only [rrStep, if_pos h0])
    · have h1 : selOf n k = 5120 := by
        have := bitAt_le_one n k
        unfold selOf; omega
      exact Challenge.EvmProof.GasSteps.cast
        (((gasSteps_rrSelCall s (sub.mpMem 6144 6144 6144 mem) n bsize esize msize k h0
              hcode hfork hrun hnp).trans
            (gasSteps_rrCallSel s (sub.mpMem 6144 6144 6144 mem) n bsize esize msize k
              hcode hfork hrun hnp)).trans
          (sub.monpro 6144 (selOf n k) 6144 (UInt256.ofNat 1615)
            (UInt256.ofNat (selOf n k) :: UInt256.ofNat k :: outer n bsize esize msize)
            (sub.mpMem 6144 6144 6144 mem) (Model.montMul mm R v v)
            (if bitAt n k = 0 then R % mm else Limbs.radix * R % mm) (by simp)
            (by omega) (by omega) (by omega) (by omega) (by omega) jumpD1615 hframe1
            hmod1 hsq hsel (Model.montMul_lt hm _ _ _)))
        rfl (by simp only [rrStep, if_neg h0, h1, retTo, rrPost])
  exact (hmid.trans hsel2).trans
    ((gasSteps_rrPost_loop s (rrStep sub.mpMem n k mem)
        n bsize esize msize k hk hk0 hcode hfork hrun hnp).trans
      (gasSteps_rrNext s (rrStep sub.mpMem n k mem)
        n bsize esize msize k k' hkk hk hcode hfork hrun hnp))

set_option linter.unusedSimpArgs false in
/-- The last iteration of the `RR` chain, with the counter at zero. -/
def gasSteps_rrLastBody (s : State) {n bsize mm minv R : Nat}
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm R minv)
    (mem : ByteArray) (esize msize v : Nat)
    (hm : 0 < mm) (hn : n ≤ 32) (hvlt : v < mm) (hframe : Frame mem n bsize minv)
    (hinv : RrInv mem n mm R v)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (rrHead s mem n bsize esize msize 0)
      (rrDone s (rrStep sub.mpMem n 0 mem) n bsize esize msize) := by
  have hbit := bitAt_le_one n 0
  have hselhi : selOf n 0 ≤ 5120 := by unfold selOf; omega
  have hsello : 4096 ≤ selOf n 0 := by unfold selOf; omega
  have hsq : Model.FastRepresents (sub.mpMem 6144 6144 6144 mem) 6144 n
      (Model.montMul mm R v v) :=
    spec.mpValue 6144 6144 6144 mem v v (by omega) (by omega) (by omega)
      hinv.modulus hframe.minvW hinv.rr hinv.rr hvlt hvlt
  have hmod1 := spec.mpFrame 6144 6144 6144 0 mm mem (by omega) (Or.inr (by omega))
    hinv.modulus
  have hr11 := spec.mpFrame 6144 6144 6144 4096 (R % mm) mem (by omega)
    (Or.inr (by omega)) hinv.r1
  have hcc1 := spec.mpFrame 6144 6144 6144 5120 (Limbs.radix * R % mm) mem (by omega)
    (Or.inr (by omega)) hinv.cc
  have hframe1 : Frame (sub.mpMem 6144 6144 6144 mem) n bsize minv :=
    sub.mpFrame 6144 6144 6144 mem (by omega) hframe
  have hsel : Model.FastRepresents (sub.mpMem 6144 6144 6144 mem) (selOf n 0) n
      (if bitAt n 0 = 0 then R % mm else Limbs.radix * R % mm) := by
    by_cases h0 : bitAt n 0 = 0
    · rw [if_pos h0, selOf, h0]; simpa using hr11
    · have h1 : bitAt n 0 = 1 := by omega
      rw [if_neg h0, selOf, h1]; simpa using hcc1
  have hmid : Challenge.EvmProof.GasSteps (rrHead s mem n bsize esize msize 0)
      (rrSel s (sub.mpMem 6144 6144 6144 mem) n bsize esize msize 0) :=
    ((gasSteps_rrHead s mem n bsize esize msize 0 hcode hfork hrun hnp).trans
      (sub.monpro 6144 6144 6144 (UInt256.ofNat 1586)
        (UInt256.ofNat 0 :: outer n bsize esize msize) mem v v (by simp)
        (by omega) (by omega) (by omega) (by omega) (by omega) jumpD1586 hframe
        hinv.modulus hinv.rr hinv.rr hvlt)).trans
      (gasSteps_rrMid s (sub.mpMem 6144 6144 6144 mem) n bsize esize msize 0 hn
        (by omega) hcode hfork hrun hnp)
  have hsel2 : Challenge.EvmProof.GasSteps
      (rrSel s (sub.mpMem 6144 6144 6144 mem) n bsize esize msize 0)
      (rrPost s (rrStep sub.mpMem n 0 mem) n bsize esize msize 0) := by
    by_cases h0 : bitAt n 0 = 0
    · exact Challenge.EvmProof.GasSteps.cast
        ((gasSteps_rrSelSkip s (sub.mpMem 6144 6144 6144 mem) n bsize esize msize 0 h0
            hcode hfork hrun hnp).trans
          (gasSteps_rrSkipSel s (sub.mpMem 6144 6144 6144 mem) n bsize esize msize 0
            hcode hfork hrun hnp))
        rfl (by simp only [rrStep, if_pos h0])
    · have h1 : selOf n 0 = 5120 := by
        have := bitAt_le_one n 0; unfold selOf; omega
      exact Challenge.EvmProof.GasSteps.cast
        (((gasSteps_rrSelCall s (sub.mpMem 6144 6144 6144 mem) n bsize esize msize 0 h0
              hcode hfork hrun hnp).trans
            (gasSteps_rrCallSel s (sub.mpMem 6144 6144 6144 mem) n bsize esize msize 0
              hcode hfork hrun hnp)).trans
          (sub.monpro 6144 (selOf n 0) 6144 (UInt256.ofNat 1615)
            (UInt256.ofNat (selOf n 0) :: UInt256.ofNat 0 :: outer n bsize esize msize)
            (sub.mpMem 6144 6144 6144 mem) (Model.montMul mm R v v)
            (if bitAt n 0 = 0 then R % mm else Limbs.radix * R % mm) (by simp)
            (by omega) (by omega) (by omega) (by omega) (by omega) jumpD1615 hframe1
            hmod1 hsq hsel (Model.montMul_lt hm _ _ _)))
        rfl (by simp only [rrStep, if_neg h0, h1, retTo, rrPost])
  exact (hmid.trans hsel2).trans
    (gasSteps_rrPost_exit s (rrStep sub.mpMem n 0 mem)
      n bsize esize msize hcode hfork hrun hnp)

/-- The five iterations with a nonzero counter. -/
def gasSteps_rrLoop (s : State) {n bsize mm minv R : Nat}
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm R minv)
    (mem : ByteArray) (esize msize : Nat)
    (hm : 0 < mm) (hcop : Nat.Coprime R mm) (hn : n ≤ 32) (hframe : Frame mem n bsize minv)
    (hinv : RrInv mem n mm R (R % mm))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (rrHead s mem n bsize esize msize 5)
      (rrHead s (rrMem sub.mpMem n mem 5) n bsize esize msize 0) :=
  Challenge.EvmProof.GasSteps.iterateBounded
    (I := rrFamily s sub.mpMem mem n bsize esize msize) 5
    (fun i hi => gasSteps_rrBody s sub spec (rrMem sub.mpMem n mem i) esize msize
      (5 - i) (5 - (i + 1)) (rrValue mm R n i) hm hn (by omega) (by omega) (by omega)
      (rrValue_lt hm i) (rrMem_frame sub mem hframe i)
      (rrMem_inv spec hm hcop hn mem hframe.minvW hinv i) hcode hfork hrun hnp)

/-- **The `RR` chain.**  Six square-and-multiply iterations starting from
`[5] ++ OUTER` at pc 1569 and ending at `RRE` (pc 1631). -/
def gasSteps_rrChain (s : State) {n bsize mm minv R : Nat}
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm R minv)
    (mem : ByteArray) (esize msize : Nat)
    (hm : 0 < mm) (hcop : Nat.Coprime R mm) (hn : n ≤ 32) (hframe : Frame mem n bsize minv)
    (hinv : RrInv mem n mm R (R % mm))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (rrHead s mem n bsize esize msize 5)
      (rrDone s (rrMem sub.mpMem n mem 6) n bsize esize msize) :=
  (gasSteps_rrLoop s sub spec mem esize msize hm hcop hn hframe hinv hcode hfork
      hrun hnp).trans
    (gasSteps_rrLastBody s sub spec (rrMem sub.mpMem n mem 5) esize msize
      (rrValue mm R n 5) hm hn (rrValue_lt hm 5) (rrMem_frame sub mem hframe 5)
      (rrMem_inv spec hm hcop hn mem hframe.minvW hinv 5) hcode hfork hrun hnp)

/-- The configuration words survive the Horner loop. -/
theorem blMems_frame {s : State} {n bsize mm minv : Nat}
    (sub : Subroutines s n bsize mm minv) (hn32 : n ≤ 32) (input : ByteArray)
    (pb : Nat) (mem : ByteArray) (hf : Frame mem n bsize minv) :
    ∀ t, Frame (blMems sub.mpMem sub.amMem input n bsize pb mem t) n bsize minv := by
  intro t
  induction t with
  | zero => exact hf
  | succ t ih =>
      exact sub.amFrame 1024 3072 1024 _ (by omega)
        (frame_storeWord (baseLimbWord input bsize pb (t + 1)) (by omega)
          (sub.mpFrame 1024 5120 1024 _ (by omega) ih))

/-- One Horner iteration: `ACC := MonPro(ACC, CC)`, store the next base limb
into `ONE`, `ACC := AddMod(ACC, ONE)`. -/
def gasSteps_blBody (s : State) {n bsize mm minv R : Nat}
    (sub : Subroutines s n bsize mm minv) (input mem : ByteArray)
    (esize msize pb j rr acc : Nat)
    (hdata : s.executionEnv.calldata = input)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hb : bsize ≤ 1024) (hpb : pb ≤ 32) (hj : 1 ≤ j)
    (hjpb : j < pb) (hle : 32 * (pb - j) ≤ bsize)
    (hact : 298 ≤ s.activeWords.toNat) (hacclt : acc < mm)
    (hframe : Frame mem n bsize minv) (hinv : BlInv mem n mm R rr acc)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (blHead s mem n bsize esize msize pb j)
      (blHead s
        (sub.amMem 1024 3072 1024
          (storeWord (sub.mpMem 1024 5120 1024 mem) (3040 + 32 * n)
            (baseLimbWord input bsize pb j)))
        n bsize esize msize pb (j + 1)) :=
  ((((gasSteps_blBodyHead s mem n bsize esize msize pb j hpb hjpb hcode hfork hrun
      hnp).trans
    (gasSteps_blMul s mem n bsize esize msize pb j hcode hfork hrun hnp)).trans
      (sub.monpro 1024 5120 1024 (UInt256.ofNat 1693)
        (UInt256.ofNat j :: UInt256.ofNat pb :: outer n bsize esize msize) mem acc
        (Limbs.radix * R % mm) (by simp) (by omega) (by omega) (by omega) (by omega)
        (by omega) jumpD1693 hframe hinv.modulus hinv.accBlock hinv.ccBlock
        hacclt)).trans
    (gasSteps_blAdd s (sub.mpMem 1024 5120 1024 mem) input n bsize esize msize pb j
      hdata hn hn32 hb hpb hj (by omega) hle hact hcode hfork hrun hnp)).trans
      ((sub.addmod 1024 3072 1024 (UInt256.ofNat 1728)
        (UInt256.ofNat j :: UInt256.ofNat pb :: outer n bsize esize msize)
        (storeWord (sub.mpMem 1024 5120 1024 mem) (3040 + 32 * n)
          (baseLimbWord input bsize pb j)) (by simp) (by omega) (by omega) (by omega)
        (by omega) (by omega) jumpD1728
        (frame_storeWord (baseLimbWord input bsize pb j) (by omega)
          (sub.mpFrame 1024 5120 1024 mem (by omega) hframe))).trans
        (gasSteps_blNext s
          (sub.amMem 1024 3072 1024
            (storeWord (sub.mpMem 1024 5120 1024 mem) (3040 + 32 * n)
              (baseLimbWord input bsize pb j)))
          n bsize esize msize pb j hcode hfork hrun hnp))

/-- The `pb - 1` Horner iterations. -/
def gasSteps_blLoop (s : State) {n bsize mm minv R : Nat}
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm R minv) (input mem : ByteArray)
    (esize msize rr : Nat)
    (hdata : s.executionEnv.calldata = input)
    (hm : 0 < mm) (hn : 2 ≤ n) (hn32 : n ≤ 32) (hcop : Nat.Coprime R mm)
    (hradix : Limbs.radix ≤ mm) (hb : bsize ≤ 1024) (hb0 : 1 ≤ bsize)
    (hact : 298 ≤ s.activeWords.toNat) (hframe : Frame mem n bsize minv)
    (hinv : BlInv mem n mm R rr
      (blValue mm (Precompile.bytesToNatPadded input 96 bsize) (pbOf bsize) 0))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (blHead s mem n bsize esize msize (pbOf bsize) 1)
      (blHead s
        (blMems sub.mpMem sub.amMem input n bsize (pbOf bsize) mem (pbOf bsize - 1))
        n bsize esize msize (pbOf bsize) (pbOf bsize - 1 + 1)) :=
  Challenge.EvmProof.GasSteps.iterateBounded
    (I := blFamily s sub.mpMem sub.amMem input mem n bsize esize msize (pbOf bsize))
    (pbOf bsize - 1)
    (fun t ht => gasSteps_blBody s sub input
      (blMems sub.mpMem sub.amMem input n bsize (pbOf bsize) mem t)
      esize msize (pbOf bsize) (t + 1) rr
      (blValue mm (Precompile.bytesToNatPadded input 96 bsize) (pbOf bsize) t)
      hdata hn hn32 hb (by unfold pbOf; omega) (by omega) (by omega)
      (by unfold pbOf; omega) hact (blValue_lt hm t)
      (blMems_frame sub hn32 input (pbOf bsize) mem hframe t)
      (blMems_inv spec hm hn hn32 hcop hradix input bsize hb0 mem hframe.minvW hinv t
        (by omega))
      hcode hfork hrun hnp)

/-- **The base chain.**  From `RRE`'s fallthrough (pc 1639) to `BDONE`
(pc 1756), leaving `b mod m` in `ACC` and `b * R mod m` in `BASE`. -/
def gasSteps_baseChain (s : State) {n bsize mm minv R : Nat}
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm R minv) (input mem : ByteArray)
    (esize msize rr : Nat)
    (hdata : s.executionEnv.calldata = input)
    (hm : 0 < mm) (hn : 2 ≤ n) (hn32 : n ≤ 32) (hcop : Nat.Coprime R mm)
    (hradix : Limbs.radix ≤ mm) (hb : bsize ≤ 1024) (hb0 : 1 ≤ bsize)
    (hact : 298 ≤ s.activeWords.toNat) (_hrrlt : rr < mm)
    (hframe : Frame mem n bsize minv)
    (hinv : BlInv
      (storeWord mem (992 + 32 * n) (UInt256.ofNat (topLimbOf input bsize)))
      n mm R rr
      (blValue mm (Precompile.bytesToNatPadded input 96 bsize) (pbOf bsize) 0))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (baseHead s mem n bsize esize msize)
      (bDone s
        (sub.mpMem 1024 6144 2048
          (blMems sub.mpMem sub.amMem input n bsize (pbOf bsize)
            (storeWord mem (992 + 32 * n) (UInt256.ofNat (topLimbOf input bsize)))
            (pbOf bsize - 1)))
        n bsize esize msize) :=
  have hframe0 : Frame
      (storeWord mem (992 + 32 * n) (UInt256.ofNat (topLimbOf input bsize)))
      n bsize minv :=
    frame_storeWord (UInt256.ofNat (topLimbOf input bsize)) (by omega) hframe
  have hfinal := blMems_inv spec hm hn hn32 hcop hradix input bsize hb0 _
    hframe0.minvW hinv (pbOf bsize - 1) (by unfold pbOf; omega)
  (((gasSteps_baseHead s mem input n bsize esize msize hdata hn hn32 hb hb0 hact hcode
      hfork hrun hnp).trans
    (Challenge.EvmProof.GasSteps.cast
      (gasSteps_blLoop s sub spec input
        (storeWord mem (992 + 32 * n) (UInt256.ofNat (topLimbOf input bsize)))
        esize msize rr hdata hm hn hn32 hcop hradix hb hb0 hact hframe0 hinv hcode
        hfork hrun hnp)
      rfl (by rw [show pbOf bsize - 1 + 1 = pbOf bsize by unfold pbOf; omega]))).trans
      ((gasSteps_blHeadExit s
        (blMems sub.mpMem sub.amMem input n bsize (pbOf bsize)
          (storeWord mem (992 + 32 * n) (UInt256.ofNat (topLimbOf input bsize)))
          (pbOf bsize - 1))
        n bsize esize msize (pbOf bsize) (pbOf bsize) (by unfold pbOf; omega)
        (by unfold pbOf; omega) le_rfl hcode hfork hrun hnp).trans
      (gasSteps_blExit s
        (blMems sub.mpMem sub.amMem input n bsize (pbOf bsize)
          (storeWord mem (992 + 32 * n) (UInt256.ofNat (topLimbOf input bsize)))
          (pbOf bsize - 1))
        n bsize esize msize (pbOf bsize) (pbOf bsize) hcode hfork hrun hnp))).trans
    ((sub.monpro 1024 6144 2048 (UInt256.ofNat 1755) (outer n bsize esize msize)
        (blMems sub.mpMem sub.amMem input n bsize (pbOf bsize)
          (storeWord mem (992 + 32 * n) (UInt256.ofNat (topLimbOf input bsize)))
          (pbOf bsize - 1))
        (blValue mm (Precompile.bytesToNatPadded input 96 bsize) (pbOf bsize)
          (pbOf bsize - 1)) rr (by simp) (by omega) (by omega) (by omega) (by omega)
        (by omega) jumpD1755
        (blMems_frame sub hn32 input (pbOf bsize) _ hframe0 (pbOf bsize - 1))
        hfinal.modulus hfinal.accBlock hfinal.rrBlock (blValue_lt hm _)).trans
      (gasSteps_bRejoin s
        (sub.mpMem 1024 6144 2048
          (blMems sub.mpMem sub.amMem input n bsize (pbOf bsize)
            (storeWord mem (992 + 32 * n) (UInt256.ofNat (topLimbOf input bsize)))
            (pbOf bsize - 1)))
        n bsize esize msize hcode hfork hrun hnp))

/-- The configuration words survive one exponent bit. -/
theorem bitStep_frame {s : State} {n bsize mm minv : Nat}
    (sub : Subroutines s n bsize mm minv) (mem : ByteArray)
    (bit : Nat) (hf : Frame mem n bsize minv) :
    Frame (bitStep sub.mpMem mem bit) n bsize minv := by
  cases bit with
  | zero => exact sub.mpFrame 1024 1024 1024 mem (by omega) hf
  | succ k =>
      exact sub.mpFrame 1024 2048 1024 _ (by omega)
        (sub.mpFrame 1024 1024 1024 mem (by omega) hf)

theorem bitMems_frame {s : State} {n bsize mm minv : Nat}
    (sub : Subroutines s n bsize mm minv) (w : Nat)
    (mem : ByteArray) (hf : Frame mem n bsize minv) :
    ∀ j, Frame (bitMems sub.mpMem w mem j) n bsize minv := by
  intro j
  induction j with
  | zero => exact hf
  | succ j ih => exact bitStep_frame sub _ (bitAt w (7 - j)) ih

theorem bitMemsFrom_frame {s : State} {n bsize mm minv : Nat}
    (sub : Subroutines s n bsize mm minv) (w : Nat) (mem : ByteArray)
    (hf : Frame mem n bsize minv) (j0 : Nat) :
    ∀ k, Frame (bitMemsFrom sub.mpMem w mem j0 k) n bsize minv := by
  intro k
  induction k with
  | zero => exact hf
  | succ k ih => exact bitStep_frame sub _ (bitAt w (7 - (j0 + k))) ih

theorem ebMems_frame {s : State} {n bsize mm minv : Nat}
    (sub : Subroutines s n bsize mm minv) (input mem : ByteArray)
    (hf : Frame mem n bsize minv) :
    ∀ i, Frame (ebMems sub.mpMem input bsize mem i) n bsize minv := by
  intro i
  induction i with
  | zero => exact hf
  | succ i ih =>
      exact bitMemsFrom_frame sub (expByte input bsize i) _ ih
        (lzSkip input bsize i) (8 - lzSkip input bsize i)


/-! ### The exponent loop, re-threaded -/

/-- One exponent bit: square `ACC`, and multiply by `BASE` when the bit is set. -/
def gasSteps_bitStep (s : State) {n bsize mm minv R : Nat}
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm R minv)
    (mem : ByteArray) (esize msize i w r bM acc : Nat)
    (hm : 0 < mm) (hn32 : n ≤ 32) (hw : w < 256) (hr : r ≤ 7) (_hbM : bM < mm)
    (hacc : acc < mm) (hframe : Frame mem n bsize minv)
    (hinv : EbInv mem n mm bM acc)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (ebitHead s mem n bsize esize msize i w (2 ^ r))
      (ebitNext s (bitStep sub.mpMem mem (bitAt w r)) n bsize esize msize i w
        (2 ^ r)) :=
  have hmask : 2 ^ r < 2 ^ 256 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hw256 : w < 2 ^ 256 := Nat.lt_of_lt_of_le hw (by norm_num)
  if h : bitAt w r = 0 then
    Challenge.EvmProof.GasSteps.cast
      (((gasSteps_ebitHead s mem n bsize esize msize i w (2 ^ r) hcode hfork hrun
          hnp).trans
        (sub.monpro 1024 1024 1024 (UInt256.ofNat 1806)
          (bitStack n bsize esize msize i w (2 ^ r)) mem acc acc (by simp [bitStack])
          (by omega) (by omega) (by omega) (by omega) (by omega) jumpD1806 hframe
          hinv.modulus hinv.accBlock hinv.accBlock hacc)).trans
        (gasSteps_ebitTestZero s (sub.mpMem 1024 1024 1024 mem) n bsize esize msize i
          w (2 ^ r) hmask hw256
          ((and_two_pow_eq_zero_iff w r).2 ((bitAt_eq_zero_iff w r).1 h))
          hcode hfork hrun hnp))
      rfl (by rw [h]; rfl)
  else
    have h1 : bitAt w r = 1 := by
      have := bitAt_le_one w r
      omega
    have hne : 2 ^ r &&& w ≠ 0 := fun hz =>
      h ((bitAt_eq_zero_iff w r).2 ((and_two_pow_eq_zero_iff w r).1 hz))
    have hsq : Model.FastRepresents (sub.mpMem 1024 1024 1024 mem) 1024 n
        (Model.montMul mm R acc acc) :=
      spec.mpValue 1024 1024 1024 mem acc acc (by omega) (by omega) (by omega)
        hinv.modulus hframe.minvW hinv.accBlock hinv.accBlock hacc hacc
    have hmod1 := spec.mpFrame 1024 1024 1024 0 mm mem (by omega) (Or.inr (by omega))
      hinv.modulus
    have hbase1 := spec.mpFrame 1024 1024 1024 2048 bM mem (by omega)
      (Or.inl (by omega)) hinv.baseBlock
    Challenge.EvmProof.GasSteps.cast
      (((((gasSteps_ebitHead s mem n bsize esize msize i w (2 ^ r) hcode hfork hrun
          hnp).trans
        (sub.monpro 1024 1024 1024 (UInt256.ofNat 1806)
          (bitStack n bsize esize msize i w (2 ^ r)) mem acc acc (by simp [bitStack])
          (by omega) (by omega) (by omega) (by omega) (by omega) jumpD1806 hframe
          hinv.modulus hinv.accBlock hinv.accBlock hacc)).trans
        (gasSteps_ebitTestOne s (sub.mpMem 1024 1024 1024 mem) n bsize esize msize i w
          (2 ^ r) hmask hw256 hne hcode hfork hrun hnp)).trans
        ((gasSteps_ebitMul s (sub.mpMem 1024 1024 1024 mem) n bsize esize msize i w
            (2 ^ r) hcode hfork hrun hnp).trans
          (sub.monpro 1024 2048 1024 (UInt256.ofNat 1831)
            (bitStack n bsize esize msize i w (2 ^ r))
            (sub.mpMem 1024 1024 1024 mem) (Model.montMul mm R acc acc) bM
            (by simp [bitStack]) (by omega) (by omega) (by omega) (by omega)
            (by omega) jumpD1831 (sub.mpFrame 1024 1024 1024 mem (by omega) hframe) hmod1 hsq
            hbase1 (Model.montMul_lt hm _ _ _)))).trans
        (gasSteps_ebitJoin s
          (sub.mpMem 1024 2048 1024 (sub.mpMem 1024 1024 1024 mem))
          n bsize esize msize i w (2 ^ r) hcode hfork hrun hnp))
      rfl (by rw [h1]; rfl)

def gasSteps_bitBody (s : State) {n bsize mm minv R : Nat}
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm R minv)
    (mem : ByteArray) (esize msize i w bM t0 j : Nat) (bits : Nat → Nat)
    (hm : 0 < mm) (hn32 : n ≤ 32) (hw : w < 256) (hj : j < 7) (hbM : bM < mm)
    (hframe : Frame (bitMems sub.mpMem w mem j) n bsize minv)
    (hinv : EbInv (bitMems sub.mpMem w mem j) n mm bM (expAcc mm R bM bits (t0 + j)))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (bitFamily s sub.mpMem mem n bsize esize msize i w j)
      (bitFamily s sub.mpMem mem n bsize esize msize i w (j + 1)) :=
  Challenge.EvmProof.GasSteps.cast
    ((gasSteps_bitStep s sub spec (bitMems sub.mpMem w mem j) esize msize i w (7 - j)
        bM (expAcc mm R bM bits (t0 + j)) hm hn32 hw (by omega) hbM
        (expAcc_lt hm bits (t0 + j)) hframe hinv hcode hfork hrun hnp).trans
      (gasSteps_ebitNextLoop s
        (bitStep sub.mpMem (bitMems sub.mpMem w mem j) (bitAt w (7 - j)))
        n bsize esize msize i w (2 ^ (7 - j)) (two_pow_ge_two (by omega))
        (two_pow_le_128 (by omega)) hcode hfork hrun hnp))
    rfl (by simp only [bitFamily, bitMems, two_pow_shift hj])

/-! ### The bit loop started at an arbitrary bit

Byte `0` enters the loop at its highest set bit rather than at bit 7.  The
skipped iterations would have squared `Mont 1`, which leaves it unchanged, so
the accumulator the loop starts from is the same one; only the memory chain has
to be re-indexed. -/

/-- The loop family, started at bit index `j0`. -/
def bitFamilyFrom (s : State) (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (mem : ByteArray) (n bsize esize msize i w j0 k : Nat) : State :=
  ebitHead s (bitMemsFrom mpMem w mem j0 k) n bsize esize msize i w
    (2 ^ (7 - j0 - k))

/-- One bit of the loop started at bit index `j0`. -/
def gasSteps_bitBodyFrom (s : State) {n bsize mm minv R : Nat}
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm R minv)
    (mem : ByteArray) (esize msize i w bM t0 j0 k : Nat) (bits : Nat → Nat)
    (hm : 0 < mm) (hn32 : n ≤ 32) (hw : w < 256) (hjk : j0 + k < 7) (hbM : bM < mm)
    (hframe : Frame (bitMemsFrom sub.mpMem w mem j0 k) n bsize minv)
    (hinv : EbInv (bitMemsFrom sub.mpMem w mem j0 k) n mm bM
      (expAcc mm R bM bits (t0 + j0 + k)))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (bitFamilyFrom s sub.mpMem mem n bsize esize msize i w j0 k)
      (bitFamilyFrom s sub.mpMem mem n bsize esize msize i w j0 (k + 1)) :=
  Challenge.EvmProof.GasSteps.cast
    ((gasSteps_bitStep s sub spec (bitMemsFrom sub.mpMem w mem j0 k) esize msize i w
        (7 - (j0 + k)) bM (expAcc mm R bM bits (t0 + j0 + k)) hm hn32 hw (by omega)
        hbM (expAcc_lt hm bits (t0 + j0 + k)) hframe hinv hcode hfork hrun hnp).trans
      (gasSteps_ebitNextLoop s
        (bitStep sub.mpMem (bitMemsFrom sub.mpMem w mem j0 k)
          (bitAt w (7 - (j0 + k))))
        n bsize esize msize i w (2 ^ (7 - (j0 + k))) (two_pow_ge_two (by omega))
        (two_pow_le_128 (by omega)) hcode hfork hrun hnp))
    (by
      simp only [bitFamilyFrom]
      rw [show 7 - j0 - k = 7 - (j0 + k) by omega])
    (by
      simp only [bitFamilyFrom, bitMemsFrom]
      rw [show 7 - j0 - (k + 1) = 7 - (j0 + k + 1) by omega,
        ← two_pow_shift (j := j0 + k) (by omega)])

/-- The loop, started at bit index `j0`: from mask `2 ^ (7 - j0)` down to `2`. -/
def gasSteps_bitLoopFrom (s : State) {n bsize mm minv R : Nat}
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm R minv)
    (mem : ByteArray) (esize msize i w bM t0 j0 : Nat) (bits : Nat → Nat)
    (hm : 0 < mm) (hn32 : n ≤ 32) (hw : w < 256) (hbM : bM < mm) (hj0 : j0 ≤ 7)
    (hbits : ∀ k, k < 8 - j0 → bits (t0 + j0 + k) = bitAt w (7 - (j0 + k)))
    (hframe : Frame mem n bsize minv)
    (hminv : MachineState.readWord mem 9376 = UInt256.ofNat minv)
    (hinv : EbInv mem n mm bM (expAcc mm R bM bits (t0 + j0)))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (ebitHead s mem n bsize esize msize i w (2 ^ (7 - j0)))
      (ebitHead s (bitMemsFrom sub.mpMem w mem j0 (7 - j0)) n bsize esize msize i w
        1) :=
  Challenge.EvmProof.GasSteps.cast
    (Challenge.EvmProof.GasSteps.iterateBounded
      (I := bitFamilyFrom s sub.mpMem mem n bsize esize msize i w j0) (7 - j0)
      (fun k hk => gasSteps_bitBodyFrom s sub spec mem esize msize i w bM t0 j0 k bits
        hm hn32 hw (by omega) hbM
        (bitMemsFrom_frame sub w mem hframe j0 k)
        (bitMemsFrom_inv spec hm hn32 bM hbM w bits t0 j0 hbits mem hminv hinv k
          (by omega))
        hcode hfork hrun hnp))
    (by simp [bitFamilyFrom, bitMemsFrom])
    (by simp [bitFamilyFrom])

/-- The first seven bits of one exponent byte. -/
def gasSteps_bitLoop (s : State) {n bsize mm minv R : Nat}
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm R minv)
    (mem : ByteArray) (esize msize i w bM t0 : Nat) (bits : Nat → Nat)
    (hm : 0 < mm) (hn32 : n ≤ 32) (hw : w < 256) (hbM : bM < mm)
    (hbits : ∀ j, j < 8 → bits (t0 + j) = bitAt w (7 - j))
    (hframe : Frame mem n bsize minv)
    (hinv : EbInv mem n mm bM (expAcc mm R bM bits t0))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (ebitHead s mem n bsize esize msize i w 128)
      (ebitHead s (bitMems sub.mpMem w mem 7) n bsize esize msize i w 1) :=
  Challenge.EvmProof.GasSteps.cast
    (Challenge.EvmProof.GasSteps.iterateBounded
      (I := bitFamily s sub.mpMem mem n bsize esize msize i w) 7
      (fun j hj => gasSteps_bitBody s sub spec mem esize msize i w bM t0 j bits hm
        hn32 hw hj hbM (bitMems_frame sub w mem hframe j)
        (bitMems_inv spec hm hn32 bM hbM w bits t0 hbits mem hframe.minvW hinv j
          (by omega))
        hcode hfork hrun hnp))
    (by simp [bitFamily, bitMems]) (by simp [bitFamily])

/-- One whole exponent byte. -/
def gasSteps_byteBody (s : State) {n bsize mm minv R : Nat}
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm R minv)
    (mem input : ByteArray) (esize msize i bM : Nat) (bits : Nat → Nat)
    (hdata : s.executionEnv.calldata = input)
    (hm : 0 < mm) (hn32 : n ≤ 32) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (hi : i < esize) (hbM : bM < mm) (hact : 298 ≤ s.activeWords.toNat)
    (hbits : ∀ j, j < 8 → bits (8 * i + j) = bitAt (expByte input bsize i) (7 - j))
    (hframe : Frame mem n bsize minv)
    (hshift : EbInv mem n mm bM
      (expAcc mm R bM bits (8 * i + lzSkip input bsize i)))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (ebHead s mem n bsize esize msize i)
      (ebHead s (byteMemAt sub.mpMem input bsize mem i) n bsize esize msize
        (i + 1)) :=
  have hwlt : expByte input bsize i < 256 :=
    (YulSemantics.EVM.byteFrom input.toList (96 + bsize + i)).toNat_lt
  have hj0 : lzSkip input bsize i ≤ 7 := lzSkip_le input bsize i
  have hlast : 7 - (lzSkip input bsize i + (7 - lzSkip input bsize i)) = 0 := by omega
  (((gasSteps_ebHeadBody s mem n bsize esize msize i he hi hcode hfork hrun hnp).trans
    (gasSteps_ebLoad s mem input n bsize esize msize i hdata hb (by omega) hact
      hframe.eoff hcode hfork hrun hnp)).trans
      (Challenge.EvmProof.GasSteps.cast
        (gasSteps_bitLoopFrom s sub spec mem esize msize i (expByte input bsize i) bM
          (8 * i) (lzSkip input bsize i) bits hm hn32 hwlt hbM hj0
          (fun k hk => by
            have := hbits (lzSkip input bsize i + k) (by omega)
            rwa [show 8 * i + (lzSkip input bsize i + k)
              = 8 * i + lzSkip input bsize i + k from by ring] at this)
          hframe hframe.minvW hshift hcode hfork hrun hnp)
        (by rw [lzMask_eq]) rfl)).trans
    (Challenge.EvmProof.GasSteps.cast
      ((gasSteps_bitStep s sub spec
          (bitMemsFrom sub.mpMem (expByte input bsize i) mem (lzSkip input bsize i)
            (7 - lzSkip input bsize i)) esize msize i
          (expByte input bsize i) 0 bM (expAcc mm R bM bits (8 * i + 7)) hm hn32 hwlt
          (by omega) hbM (expAcc_lt hm bits (8 * i + 7))
          (bitMemsFrom_frame sub (expByte input bsize i) mem hframe
            (lzSkip input bsize i) (7 - lzSkip input bsize i))
          (by
            have h := bitMemsFrom_inv spec hm hn32 bM hbM (expByte input bsize i) bits
              (8 * i) (lzSkip input bsize i)
              (fun k hk => by
                have := hbits (lzSkip input bsize i + k) (by omega)
                rwa [show 8 * i + (lzSkip input bsize i + k)
                  = 8 * i + lzSkip input bsize i + k from by ring] at this)
              mem hframe.minvW hshift (7 - lzSkip input bsize i) (by omega)
            rwa [show 8 * i + lzSkip input bsize i + (7 - lzSkip input bsize i)
              = 8 * i + 7 from by omega] at h)
          hcode hfork hrun hnp).trans
        ((gasSteps_ebitNextExit s
            (bitStep sub.mpMem
              (bitMemsFrom sub.mpMem (expByte input bsize i) mem (lzSkip input bsize i)
                (7 - lzSkip input bsize i)) (bitAt (expByte input bsize i) 0))
            n bsize esize msize i (expByte input bsize i) hcode hfork hrun hnp).trans
          (gasSteps_ebTail s
            (bitStep sub.mpMem
              (bitMemsFrom sub.mpMem (expByte input bsize i) mem (lzSkip input bsize i)
                (7 - lzSkip input bsize i)) (bitAt (expByte input bsize i) 0))
            n bsize esize msize i (expByte input bsize i) hcode hfork hrun hnp)))
      (by norm_num)
      (by
        simp only [byteMemAt]
        rw [show 8 - lzSkip input bsize i = 7 - lzSkip input bsize i + 1 from by omega]
        simp only [bitMemsFrom, hlast]))

/-- **The exponent loop.**  All `8 * esize` bits. -/
def gasSteps_ebLoop (s : State) {n bsize mm minv R : Nat}
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm R minv)
    (mem input : ByteArray) (esize msize bM : Nat)
    (hdata : s.executionEnv.calldata = input)
    (hm : 0 < mm) (hcop : Nat.Coprime R mm) (hn32 : n ≤ 32) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (hbM : bM < mm) (hact : 298 ≤ s.activeWords.toNat)
    (hframe : Frame mem n bsize minv)
    (hinv : EbInv mem n mm bM (expAcc mm R bM (expBits input bsize) 0))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (ebHead s mem n bsize esize msize 0)
      (ebHead s (ebMems sub.mpMem input bsize mem esize) n bsize esize msize esize) :=
  Challenge.EvmProof.GasSteps.iterateBounded
    (I := ebFamily s sub.mpMem input mem n bsize esize msize) esize
    (fun i hi => gasSteps_byteBody s sub spec
      (ebMems sub.mpMem input bsize mem i) input esize msize i bM
      (expBits input bsize) hdata hm hn32 hb he hi hbM hact
      (fun j hj => expBits_eq input bsize i j hj)
      (ebMems_frame sub input mem hframe i)
      (ebInv_shift (n := n) (bM := bM) hm hcop input bsize i
        (ebMems sub.mpMem input bsize mem i)
        (ebMems_inv spec hm hcop hn32 bM hbM input bsize mem hframe.minvW hinv i))
      hcode hfork hrun hnp)

/-- **The exponent chain.**  From `BDONE` (pc 1756) to the `RETURN` at pc 1885. -/
def gasSteps_expChain (s : State) {n bsize mm minv R : Nat}
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm R minv)
    (mem input : ByteArray) (esize msize bM : Nat)
    (hdata : s.executionEnv.calldata = input)
    (hm : 0 < mm) (hcop : Nat.Coprime R mm) (hn : 2 ≤ n) (hn32 : n ≤ 32) (hb : bsize ≤ 1024)
    (he : esize ≤ 1024) (hmz : 32 < msize) (hm32 : msize ≤ 32 * n)
    (_hradix : Limbs.radix ≤ mm) (hbM : bM < mm)
    (hact : 298 ≤ s.activeWords.toNat) (hframe : Frame mem n bsize minv)
    (hinv : EbInv (mcopyMem mem 1024 4096 (32 * n)) n mm bM
      (expAcc mm R bM (expBits input bsize) 0))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (bDone s mem n bsize esize msize)
      (returnedState s
        (sub.mpMem 1024 3072 1024
          (storeWord
            (ebMems sub.mpMem input bsize (mcopyMem mem 1024 4096 (32 * n)) esize)
            (3040 + 32 * n) (UInt256.ofNat 1)))
        n bsize esize msize) :=
  have hframe0 : Frame (mcopyMem mem 1024 4096 (32 * n)) n bsize minv :=
    frame_mcopyMem (by omega) hframe
  have hloop := ebMems_inv spec hm hcop hn32 bM hbM input bsize
    (mcopyMem mem 1024 4096 (32 * n)) hframe0.minvW hinv esize
  have hframeE : Frame
      (ebMems sub.mpMem input bsize (mcopyMem mem 1024 4096 (32 * n)) esize)
      n bsize minv :=
    ebMems_frame sub input (mcopyMem mem 1024 4096 (32 * n)) hframe0 esize
  have hframeS : Frame
      (storeWord
        (ebMems sub.mpMem input bsize (mcopyMem mem 1024 4096 (32 * n)) esize)
        (3040 + 32 * n) (UInt256.ofNat 1)) n bsize minv :=
    frame_storeWord (UInt256.ofNat 1) (by omega) hframeE
  have hone : Model.FastRepresents
      (storeWord
        (ebMems sub.mpMem input bsize (mcopyMem mem 1024 4096 (32 * n)) esize)
        (3040 + 32 * n) (UInt256.ofNat 1)) 3072 n 1 := by
    obtain ⟨one, honelt, honerep⟩ := hloop.oneBlock
    have h := write_low_limb (UInt256.ofNat 1) (by omega) honerep honelt
    rwa [show (UInt256.ofNat 1).toNat = 1 from by decide] at h
  have hmodS := storeWord_frame
    (ebMems sub.mpMem input bsize (mcopyMem mem 1024 4096 (32 * n)) esize)
    (3040 + 32 * n) 0 n mm (UInt256.ofNat 1) (Or.inr (by omega)) hloop.modulus
  have haccS := storeWord_frame
    (ebMems sub.mpMem input bsize (mcopyMem mem 1024 4096 (32 * n)) esize)
    (3040 + 32 * n) 1024 n (expAcc mm R bM (expBits input bsize) (8 * esize))
    (UInt256.ofNat 1) (Or.inr (by omega)) hloop.accBlock
  ((((gasSteps_bDone s mem n bsize esize msize hn hn32 hact hframe.s32 hcode hfork
      hrun hnp).trans
    (gasSteps_ebLoop s sub spec (mcopyMem mem 1024 4096 (32 * n)) input esize msize
      bM hdata hm hcop hn32 hb he hbM hact hframe0 hinv hcode hfork hrun hnp)).trans
      (gasSteps_ebHeadExit s
        (ebMems sub.mpMem input bsize (mcopyMem mem 1024 4096 (32 * n)) esize)
        n bsize esize msize esize he (by omega) le_rfl hcode hfork hrun hnp)).trans
    ((gasSteps_ebEnd s
        (ebMems sub.mpMem input bsize (mcopyMem mem 1024 4096 (32 * n)) esize)
        n bsize esize msize esize hn hn32 hact hcode hfork hrun hnp).trans
      (sub.monpro 1024 3072 1024 (UInt256.ofNat 1876) (outer n bsize esize msize)
        (storeWord
          (ebMems sub.mpMem input bsize (mcopyMem mem 1024 4096 (32 * n)) esize)
          (3040 + 32 * n) (UInt256.ofNat 1))
        (expAcc mm R bM (expBits input bsize) (8 * esize)) 1 (by simp) (by omega)
        (by omega) (by omega) (by omega) (by omega) jumpD1876 hframeS hmodS haccS
        hone (expAcc_lt hm _ _)))).trans
    (gasSteps_return s
      (sub.mpMem 1024 3072 1024
        (storeWord
          (ebMems sub.mpMem input bsize (mcopyMem mem 1024 4096 (32 * n)) esize)
          (3040 + 32 * n) (UInt256.ofNat 1)))
      n bsize esize msize hn hn32 hmz hm32 hact hcode hfork hrun hnp)


/-! ### The hand-over from `Fast.Setup`, re-threaded -/

/-- **From `Fast.Setup`'s hand-over state to the `RR` chain.**  `dbl` is the
`DOUBLE256` contract `Fast.Double.gasSteps_double256_addmod` provides, and
`dblFrame` its configuration-word preservation. -/
def gasSteps_setupToRR (s : State) {n bsize mm minv : Nat}
    (_sub : Subroutines s n bsize mm minv) (mem : ByteArray) (esize msize : Nat)
    (dblF ccF : Nat → ByteArray → ByteArray)
    (dbl : ∀ (ret : UInt256) (mem' : ByteArray),
      Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true →
      Frame mem' n bsize minv →
      Challenge.EvmProof.GasSteps (r1Call s mem' 4096 ret n bsize esize msize)
        (retTo s (dblF 4096 mem') ret (outer n bsize esize msize)))
    (cc : ∀ (ret : UInt256) (mem' : ByteArray) (y' : Nat),
      Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true →
      Frame mem' n bsize minv →
      Model.FastRepresents mem' 0 n mm →
      Model.FastRepresents mem' 5120 n y' → y' < mm →
      Challenge.EvmProof.GasSteps (ccCall s mem' 5120 ret n bsize esize msize)
        (retTo s (ccF 5120 mem') ret (outer n bsize esize msize)))
    (dblFrame : ∀ mem' : ByteArray,
      Frame mem' n bsize minv → Frame (dblF 4096 mem') n bsize minv)
    (ccFrame : ∀ mem' : ByteArray,
      Frame mem' n bsize minv → Frame (ccF 5120 mem') n bsize minv)
    (y : Nat)
    (hmod2 : Model.FastRepresents (mcopyMem (dblF 4096 mem) 5120 4096 (32 * n)) 0 n mm)
    (hy2 : Model.FastRepresents (mcopyMem (dblF 4096 mem) 5120 4096 (32 * n)) 5120 n y)
    (hylt : y < mm)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hact : 298 ≤ s.activeWords.toNat)
    (hframe : Frame mem n bsize minv)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (r1Call s mem 4096 (UInt256.ofNat 1533) n bsize esize msize)
      (rrHead s (setupToRRMem dblF ccF n mem) n bsize esize msize 5) :=
  have hf1 : Frame (dblF 4096 mem) n bsize minv := dblFrame mem hframe
  have hf2 : Frame (mcopyMem (dblF 4096 mem) 5120 4096 (32 * n)) n bsize minv :=
    frame_mcopyMem (by omega) hf1
  have hf3 : Frame (ccF 5120 (mcopyMem (dblF 4096 mem) 5120 4096 (32 * n)))
      n bsize minv := ccFrame _ hf2
  (((dbl (UInt256.ofNat 1533) mem jumpD1533 hframe).trans
    (gasSteps_r0 s (dblF 4096 mem) n bsize esize msize hn hn32 hact hf1.s32 hcode
      hfork hrun hnp)).trans
      (cc (UInt256.ofNat 1555)
        (mcopyMem (dblF 4096 mem) 5120 4096 (32 * n)) y jumpD1555 hf2 hmod2 hy2
        hylt)).trans
    (gasSteps_r1 s (ccF 5120 (mcopyMem (dblF 4096 mem) 5120 4096 (32 * n)))
      n bsize esize msize hn hn32 hact hf3.s32 hcode hfork hrun hnp)


/-! ## Blocks the loops leave untouched

`rrMem` writes only `RR`; `blMems` writes only `ACC` and the `ONE` scratch
slot.  Both therefore carry an arbitrary disjoint block through. -/

theorem rrMem_preserves {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (ptr v : Nat)
    (hptr : ptr + 32 * n ≤ 6144) (mem : ByteArray)
    (hrep : Model.FastRepresents mem ptr n v) :
    ∀ i, Model.FastRepresents (rrMem mpMem n mem i) ptr n v := by
  intro i
  induction i with
  | zero => exact hrep
  | succ i ih =>
      show Model.FastRepresents (rrStep mpMem n (5 - i) (rrMem mpMem n mem i)) ptr n v
      unfold rrStep
      split
      · exact spec.mpFrame 6144 6144 6144 ptr v _ (by omega) (by omega) ih
      · exact spec.mpFrame 6144 5120 6144 ptr v _ (by omega) (by omega)
          (spec.mpFrame 6144 6144 6144 ptr v _ (by omega) (by omega) ih)

theorem blMems_preserves {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R minv : Nat} (spec : SubSpec mpMem amMem n mm R minv)
    (input : ByteArray) (bsize pb ptr v : Nat) (hlo : 3072 + 32 * n ≤ ptr)
    (hhi : ptr + 32 * n ≤ 7168) (mem : ByteArray)
    (hrep : Model.FastRepresents mem ptr n v) :
    ∀ t, Model.FastRepresents (blMems mpMem amMem input n bsize pb mem t) ptr n v := by
  intro t
  induction t with
  | zero => exact hrep
  | succ t ih =>
      rw [blMems_succ, blStepMem]
      exact spec.amFrame 1024 3072 1024 ptr v _ (by omega) (by omega)
        (storeWord_frame _ (3040 + 32 * n) ptr n v _ (Or.inl (by omega))
          (spec.mpFrame 1024 5120 1024 ptr v _ (by omega) (by omega) ih))

/-! ## From `bDone` to the `RETURN`

Both branches of the `bsize = 0` test reach `bDone` with `BASE` holding the
Montgomery form of the base; from there the exponent loop and the packaging
are shared. -/

theorem handled_of_bDone (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize mm minv bM : Nat)
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hdata : s.executionEnv.calldata = input) (hstack : s.callStack = [])
    (hact : 298 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (hmz : 32 < msize) (hm32 : msize ≤ 32 * n)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hmm : mm = Precompile.bytesToNatPadded input (96 + bsize + esize) msize)
    (hodd : mm % 2 = 1) (hradix : Limbs.radix ≤ mm) (hbMlt : bM < mm)
    (hbMform : bM ≡ Precompile.bytesToNatPadded input 96 bsize * Limbs.radix ^ n [MOD mm])
    (hframe : Frame mem n bsize minv)
    (hEb : EbInv (mcopyMem mem 1024 4096 (32 * n)) n mm bM
      (expAcc mm (Limbs.radix ^ n) bM (expBits input bsize) 0)) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps
        (bDone s mem n bsize esize msize) final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) := by
  have hmpos : 0 < mm := lt_of_lt_of_le Limbs.radix_pos hradix
  have hcop : Nat.Coprime (Limbs.radix ^ n) mm := Model.coprime_radix_pow_of_odd hodd n
  have hframeC : Frame (mcopyMem mem 1024 4096 (32 * n)) n bsize minv :=
    frame_mcopyMem (by omega) hframe
  have htrace := gasSteps_expChain s sub spec mem input esize msize bM hdata hmpos hcop hn hn32
    hb he hmz hm32 hradix hbMlt hact hframe hEb hcode hfork hrun hnp
  have hfinal := ebMem_final spec hmpos hn hn32 hcop hradix hbMlt hbMform input bsize esize
    rfl (mcopyMem mem 1024 4096 (32 * n)) hframeC.minvW hEb
  refine handled_of_trace input (bDone s mem n bsize esize msize) s _ n bsize esize msize
    _ hstack htrace hn hm32 (by omega) hbsize hesize hmsz hfinal ?_
  rw [hmm]

/-! ## The base loop -/

theorem handled_of_baseHead (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize mm minv rr : Nat)
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hdata : s.executionEnv.calldata = input) (hstack : s.callStack = [])
    (hact : 298 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hb : bsize ≤ 1024) (hb0 : 1 ≤ bsize)
    (he : esize ≤ 1024) (hmz : 32 < msize) (hm32 : msize ≤ 32 * n)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hmm : mm = Precompile.bytesToNatPadded input (96 + bsize + esize) msize)
    (hodd : mm % 2 = 1) (hradix : Limbs.radix ≤ mm)
    (hrrlt : rr < mm)
    (hrrmod : rr ≡ Limbs.radix ^ n * Limbs.radix ^ n [MOD mm])
    (hframe : Frame mem n bsize minv)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hr1 : Model.FastRepresents mem 4096 n (Limbs.radix ^ n % mm))
    (hcc : Model.FastRepresents mem 5120 n (Limbs.radix * Limbs.radix ^ n % mm))
    (hrrb : Model.FastRepresents mem 6144 n rr)
    (hacc : Model.FastRepresents mem 1024 n 0)
    (hone : Model.FastRepresents mem 3072 n 0) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps
        (baseHead s mem n bsize esize msize) final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) := by
  have hmpos : 0 < mm := lt_of_lt_of_le Limbs.radix_pos hradix
  have hcop : Nat.Coprime (Limbs.radix ^ n) mm := Model.coprime_radix_pow_of_odd hodd n
  have htlt : topLimbOf input bsize < Limbs.radix := by
    have h := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input 96 (topWidth bsize)
    have hw : topWidth bsize ≤ 32 := by unfold topWidth pbOf; omega
    have hp : (256 : Nat) ^ topWidth bsize ≤ 256 ^ 32 :=
      Nat.pow_le_pow_right (by norm_num) hw
    have hr : (256 : Nat) ^ 32 = Limbs.radix := Limbs.radix_eq.symm
    unfold topLimbOf
    omega
  have htlt' : topLimbOf input bsize < 2 ^ 256 := htlt
  have hbv : blValue mm (Precompile.bytesToNatPadded input 96 bsize) (pbOf bsize) 0 =
      topLimbOf input bsize := by
    show Precompile.bytesToNatPadded input 96 bsize /
      Limbs.radix ^ (pbOf bsize - 1) % mm = _
    rw [← topLimbOf_value input bsize hb0,
      Nat.mod_eq_of_lt (lt_of_lt_of_le htlt hradix)]
  have haccI : Model.FastRepresents
      (storeWord mem (992 + 32 * n) (UInt256.ofNat (topLimbOf input bsize))) 1024 n
      (blValue mm (Precompile.bytesToNatPadded input 96 bsize) (pbOf bsize) 0) := by
    have h := Model.fastRepresents_write_low_of_zero
      (UInt256.ofNat (topLimbOf input bsize)) hacc (by omega)
    rw [show (1024 : Nat) + 32 * (n - 1) = 992 + 32 * n from by omega] at h
    have hval : (UInt256.ofNat (topLimbOf input bsize)).toNat =
        blValue mm (Precompile.bytesToNatPadded input 96 bsize) (pbOf bsize) 0 := by
      rw [hbv, toNat_ofNat_self htlt']
    rw [← hval]
    exact h
  have hframeS : Frame
      (storeWord mem (992 + 32 * n) (UInt256.ofNat (topLimbOf input bsize)))
      n bsize minv :=
    frame_storeWord (UInt256.ofNat (topLimbOf input bsize)) (by omega) hframe
  have hBl : BlInv
      (storeWord mem (992 + 32 * n) (UInt256.ofNat (topLimbOf input bsize))) n mm
      (Limbs.radix ^ n) rr
      (blValue mm (Precompile.bytesToNatPadded input 96 bsize) (pbOf bsize) 0) :=
    ⟨storeWord_frame _ (992 + 32 * n) 0 n mm _ (Or.inr (by omega)) hmod,
     haccI,
     ⟨0, Limbs.radix_pos,
       storeWord_frame _ (992 + 32 * n) 3072 n 0 _ (Or.inl (by omega)) hone⟩,
     storeWord_frame _ (992 + 32 * n) 5120 n _ _ (Or.inl (by omega)) hcc,
     storeWord_frame _ (992 + 32 * n) 6144 n _ _ (Or.inl (by omega)) hrrb⟩
  have htrace := gasSteps_baseChain s sub spec input mem esize msize rr hdata hmpos hn hn32
    hcop hradix hb hb0 hact hrrlt hframe hBl hcode hfork hrun hnp
  have hblInv := blMems_inv spec hmpos hn hn32 hcop hradix input bsize hb0
    (storeWord mem (992 + 32 * n) (UInt256.ofNat (topLimbOf input bsize)))
    hframeS.minvW hBl (pbOf bsize - 1) (by unfold pbOf; omega)
  have hframeB : Frame
      (blMems sub.mpMem sub.amMem input n bsize (pbOf bsize)
        (storeWord mem (992 + 32 * n) (UInt256.ofNat (topLimbOf input bsize)))
        (pbOf bsize - 1)) n bsize minv :=
    blMems_frame sub hn32 input (pbOf bsize)
      (storeWord mem (992 + 32 * n) (UInt256.ofNat (topLimbOf input bsize)))
      hframeS (pbOf bsize - 1)
  have haccB := blMem_final spec hmpos hn hn32 hcop hradix input bsize hb0
    (storeWord mem (992 + 32 * n) (UInt256.ofNat (topLimbOf input bsize)))
    hframeS.minvW hBl
  have hr1B : Model.FastRepresents
      (blMems sub.mpMem sub.amMem input n bsize (pbOf bsize)
        (storeWord mem (992 + 32 * n) (UInt256.ofNat (topLimbOf input bsize)))
        (pbOf bsize - 1)) 4096 n (Limbs.radix ^ n % mm) :=
    blMems_preserves spec input bsize (pbOf bsize) 4096 (Limbs.radix ^ n % mm)
      (by omega) (by omega)
      (storeWord mem (992 + 32 * n) (UInt256.ofNat (topLimbOf input bsize)))
      (storeWord_frame mem (992 + 32 * n) 4096 n _ _ (Or.inl (by omega)) hr1)
      (pbOf bsize - 1)
  have hbM := blMem_base spec hmpos hn32 hcop hrrmod hrrlt
    (blMems sub.mpMem sub.amMem input n bsize (pbOf bsize)
      (storeWord mem (992 + 32 * n) (UInt256.ofNat (topLimbOf input bsize)))
      (pbOf bsize - 1))
    hframeB.minvW hblInv.modulus haccB hblInv.rrBlock
  have hframe7 : Frame
      (sub.mpMem 1024 6144 2048
        (blMems sub.mpMem sub.amMem input n bsize (pbOf bsize)
          (storeWord mem (992 + 32 * n) (UInt256.ofNat (topLimbOf input bsize)))
          (pbOf bsize - 1))) n bsize minv :=
    sub.mpFrame 1024 6144 2048 _ (by omega) hframeB
  have hEb : EbInv
      (mcopyMem
        (sub.mpMem 1024 6144 2048
          (blMems sub.mpMem sub.amMem input n bsize (pbOf bsize)
            (storeWord mem (992 + 32 * n) (UInt256.ofNat (topLimbOf input bsize)))
            (pbOf bsize - 1))) 1024 4096 (32 * n)) n mm
      (Precompile.bytesToNatPadded input 96 bsize * Limbs.radix ^ n % mm)
      (expAcc mm (Limbs.radix ^ n)
        (Precompile.bytesToNatPadded input 96 bsize * Limbs.radix ^ n % mm)
        (expBits input bsize) 0) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Csub.fastRepresents_mcopy_disjoint _ 4096 1024 (32 * n) 0 n mm (by omega)
        (spec.mpFrame 1024 6144 2048 0 mm _ (by omega) (by omega) hblInv.modulus)
    · exact Csub.fastRepresents_mcopy _ 4096 1024 n (Limbs.radix ^ n % mm) (by omega)
        (spec.mpFrame 1024 6144 2048 4096 (Limbs.radix ^ n % mm) _ (by omega)
          (by omega) hr1B)
    · exact Csub.fastRepresents_mcopy_disjoint _ 4096 1024 (32 * n) 2048 n _
        (by omega) hbM
    · obtain ⟨one, honelt, honerep⟩ := hblInv.oneBlock
      exact ⟨one, honelt,
        Csub.fastRepresents_mcopy_disjoint _ 4096 1024 (32 * n) 3072 n one (by omega)
          (spec.mpFrame 1024 6144 2048 3072 one _ (by omega) (by omega) honerep)⟩
  obtain ⟨final, ⟨tr⟩, hdone, hres⟩ :=
    handled_of_bDone input s
      (sub.mpMem 1024 6144 2048
        (blMems sub.mpMem sub.amMem input n bsize (pbOf bsize)
          (storeWord mem (992 + 32 * n) (UInt256.ofNat (topLimbOf input bsize)))
          (pbOf bsize - 1))) n bsize esize msize mm minv
      (Precompile.bytesToNatPadded input 96 bsize * Limbs.radix ^ n % mm) sub spec
      hcode hfork hrun hnp hdata hstack hact hn hn32 hb he hmz hm32 hbsize hesize hmsz
      hmm hodd hradix (Nat.mod_lt _ hmpos) (Nat.mod_modEq _ _) hframe7 hEb
  exact ⟨final, ⟨htrace.trans tr⟩, hdone, hres⟩

/-! ## From the head of the `RR` loop to the `RETURN` -/

theorem handled_of_rrHead (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize mm minv : Nat)
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hdata : s.executionEnv.calldata = input) (hstack : s.callStack = [])
    (hact : 298 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (hmz : 32 < msize) (hm32 : msize ≤ 32 * n)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hmm : mm = Precompile.bytesToNatPadded input (96 + bsize + esize) msize)
    (hodd : mm % 2 = 1) (hradix : Limbs.radix ≤ mm)
    (hframe : Frame mem n bsize minv)
    (hinv : RrInv mem n mm (Limbs.radix ^ n) (Limbs.radix ^ n % mm))
    (hacc0 : Model.FastRepresents mem 1024 n 0)
    (hbase0 : Model.FastRepresents mem 2048 n 0)
    (hone0 : Model.FastRepresents mem 3072 n 0) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps
        (rrHead s mem n bsize esize msize 5) final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) := by
  have hmpos : 0 < mm := lt_of_lt_of_le Limbs.radix_pos hradix
  have hcop : Nat.Coprime (Limbs.radix ^ n) mm := Model.coprime_radix_pow_of_odd hodd n
  have hrr := gasSteps_rrChain s sub spec mem esize msize hmpos hcop hn32 hframe hinv
    hcode hfork hrun hnp
  have hframe6 : Frame (rrMem sub.mpMem n mem 6) n bsize minv := rrMem_frame sub mem hframe 6
  have hinv6 := rrMem_inv spec hmpos hcop hn32 mem hframe.minvW hinv 6
  have hrrlt : rrValue mm (Limbs.radix ^ n) n 6 < mm := rrValue_lt hmpos 6
  have hrrmod : rrValue mm (Limbs.radix ^ n) n 6 ≡
      Limbs.radix ^ n * Limbs.radix ^ n [MOD mm] := rrValue_final hmpos hcop hn32
  have hacc6 : Model.FastRepresents (rrMem sub.mpMem n mem 6) 1024 n 0 :=
    rrMem_preserves spec 1024 0 (by omega) mem hacc0 6
  have hbase6 : Model.FastRepresents (rrMem sub.mpMem n mem 6) 2048 n 0 :=
    rrMem_preserves spec 2048 0 (by omega) mem hbase0 6
  have hone6 : Model.FastRepresents (rrMem sub.mpMem n mem 6) 3072 n 0 :=
    rrMem_preserves spec 3072 0 (by omega) mem hone0 6
  rcases Nat.eq_zero_or_pos bsize with hb0 | hb0
  · subst hb0
    have hEb : EbInv (mcopyMem (rrMem sub.mpMem n mem 6) 1024 4096 (32 * n)) n mm 0
        (expAcc mm (Limbs.radix ^ n) 0 (expBits input 0) 0) := by
      refine ⟨?_, ?_, ?_, ⟨0, Limbs.radix_pos, ?_⟩⟩
      · exact Csub.fastRepresents_mcopy_disjoint _ 4096 1024 (32 * n) 0 n mm
          (by omega) hinv6.modulus
      · exact Csub.fastRepresents_mcopy _ 4096 1024 n (Limbs.radix ^ n % mm)
          (by omega) hinv6.r1
      · exact Csub.fastRepresents_mcopy_disjoint _ 4096 1024 (32 * n) 2048 n 0
          (by omega) hbase6
      · exact Csub.fastRepresents_mcopy_disjoint _ 4096 1024 (32 * n) 3072 n 0
          (by omega) hone6
    obtain ⟨final, ⟨tr⟩, hdone, hres⟩ :=
      handled_of_bDone input s (rrMem sub.mpMem n mem 6) n 0 esize msize mm minv 0
        sub spec hcode hfork hrun hnp hdata hstack hact hn hn32 (by omega) he hmz hm32
        hbsize hesize hmsz hmm hodd hradix hmpos (by simpa using Nat.ModEq.refl 0) hframe6 hEb
    exact ⟨final, ⟨(hrr.trans (gasSteps_rrDone_skip s (rrMem sub.mpMem n mem 6) n esize
      msize hcode hfork hrun hnp)).trans tr⟩, hdone, hres⟩
  · obtain ⟨final, ⟨tr⟩, hdone, hres⟩ :=
      handled_of_baseHead input s (rrMem sub.mpMem n mem 6) n bsize esize msize mm minv
        (rrValue mm (Limbs.radix ^ n) n 6) sub spec hcode hfork hrun hnp hdata hstack hact
        hn hn32 hb hb0 he hmz hm32 hbsize hesize hmsz hmm hodd hradix hrrlt hrrmod hframe6
        hinv6.modulus hinv6.r1 hinv6.cc hinv6.rr hacc6 hone6
    exact ⟨final, ⟨(hrr.trans (gasSteps_rrDone_base s (rrMem sub.mpMem n mem 6) n bsize
      esize msize hb (by omega) hcode hfork hrun hnp)).trans tr⟩, hdone, hres⟩


/-! ## The concrete subroutine instance

`MONPRO` comes from `Fast.Monpro.gasSteps_monproFull`, `ADDMOD` from the pair
`Fast.Csub.gasSteps_addmod` / `gasSteps_csub` packaged as `gasSteps_addmodFull`. -/

/-- The `MONPRO` step of the concrete instance. -/
def subsMonpro (s : State) (n bsize mm minv : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hmpos : 0 < mm) (hminvlt : minv < 2 ^ 256)
    (hminvA : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0) :
    ∀ (pa pb pd : Nat) (ret : UInt256) (tail : List UInt256)
      (mem : ByteArray) (a b : Nat), tail.length ≤ 1000 →
      32 ≤ pa → pa + 32 * n ≤ 8192 → 32 ≤ pb → pb + 32 * n ≤ 8192 →
      pd + 32 * n ≤ 8192 →
      Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true →
      Frame mem n bsize minv → Model.FastRepresents mem 0 n mm →
      Model.FastRepresents mem pa n a → Model.FastRepresents mem pb n b → a < mm →
      Challenge.EvmProof.GasSteps (mpCall s mem pa pb pd ret tail)
        (retTo s (Monpro.monproMem s mem pa pb n pd) ret tail) := by
  intro pa pb pd ret tail mem a b hcap hpa hpaFit hpb hpbFit hpdFit hjump hf hm ha hb ham
  -- `GasSteps` lives in `Type`, so the limb count has to be split by `cases`.
  cases n with
  | zero => exact absurd hn (by omega)
  | succ n1 =>
    cases n1 with
    | zero => exact absurd hn (by omega)
    | succ p =>
      have hpdN : (UInt256.ofNat pd).toNat = pd :=
        toNat_ofNat_self (Nat.lt_of_le_of_lt (show pd ≤ 8192 by omega) (by norm_num))
      have hlow : (MachineState.readWord mem (32 * (p + 2) - 32)).toNat =
          mm % Limbs.radix := by
        have h := Model.readWord_of_fastRepresents hm (j := p + 1) (by omega)
        rw [show (0 : Nat) + 32 * (p + 1) = 32 * (p + 2) - 32 from by omega,
          show p + 1 + 1 - 1 - (p + 1) = 0 from by omega, pow_zero, Nat.div_one] at h
        exact h
      have hmi : (MachineState.readWord mem 9376).toNat = minv := by
        rw [hf.minvW, toNat_ofNat_self hminvlt]
      exact Challenge.EvmProof.GasSteps.cast
        (Monpro.gasSteps_monproFull s mem pa pb p a b mm (UInt256.ofNat pd) ret tail
          (by omega) hrun hcode hfork hnp hact hn32 hpa hpaFit hpb hpbFit hcds
          hf.s32 hf.tl hf.ml hjump (by omega) ha hb hm ham hmpos
          (by rw [hlow, hmi]; exact hminvA))
        rfl
        (by simp only [Csub.csReturnedState, retTo, Monpro.monproMem_def,
          Csub.csResultMemory, hpdN])

/-- The `ADDMOD` step of the concrete instance. -/
def subsAddmod (s : State) (n bsize minv : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32) :
    ∀ (pa pb pd : Nat) (ret : UInt256) (tail : List UInt256) (mem : ByteArray),
      tail.length ≤ 1000 →
      32 ≤ pa → pa + 32 * n ≤ 8192 → 32 ≤ pb → pb + 32 * n ≤ 8192 →
      pd + 32 * n ≤ 8192 →
      Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true →
      Frame mem n bsize minv →
      Challenge.EvmProof.GasSteps (amCall s mem pa pb pd ret tail)
        (retTo s (amMemOf mem pa pb n pd) ret tail) :=
  fun pa pb pd ret tail mem hcap hpa hpaFit hpb hpbFit hpdFit hjump hf =>
    gasSteps_addmodFull s mem pa pb n pd ret tail (by omega) hcode hfork hrun hnp hact
      hn hn32 hpa hpaFit hpb hpbFit hpdFit hjump hf.s32 hf.ml hf.tl

/-- The concrete pair of subroutine contracts. -/
def subs (s : State) (n bsize mm minv : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hmpos : 0 < mm) (hminvlt : minv < 2 ^ 256)
    (hminvA : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0) :
    Subroutines s n bsize mm minv where
  mpMem pa pb pd mem := Monpro.monproMem s mem pa pb n pd
  amMem pa pb pd mem := amMemOf mem pa pb n pd
  mpFrame pa pb pd mem hpd hf := monproMem_frame' pa pb pd (by omega) hn32 (by omega) hf
  amFrame pa pb pd mem hpd hf := amMemOf_frame pa pb pd (by omega) hn32 (by omega) hf
  monpro := subsMonpro s n bsize mm minv hcode hfork hrun hnp hact hcds hn hn32 hmpos
    hminvlt hminvA
  addmod := subsAddmod s n bsize minv hcode hfork hrun hnp hact hn hn32

/-- The value-level contract the concrete pair satisfies. -/
theorem specOf (s : State) (n mm minv : Nat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hodd : mm % 2 = 1) (hmpos : 0 < mm) (hminvlt : minv < 2 ^ 256)
    (hminvA : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0) :
    SubSpec (fun pa pb pd mem => Monpro.monproMem s mem pa pb n pd)
      (fun pa pb pd mem => amMemOf mem pa pb n pd) n mm (Limbs.radix ^ n) minv where
  mpValue pa pb pd mem a b hpa hpb hpd hm hminv ha hb ham hbm := by
    have hlow : (MachineState.readWord mem (32 * n - 32)).toNat = mm % Limbs.radix := by
      have h := Model.readWord_of_fastRepresents hm (j := n - 1) (by omega)
      rw [show (0 : Nat) + 32 * (n - 1) = 32 * n - 32 from by omega,
        show n - 1 - (n - 1) = 0 from by omega, pow_zero, Nat.div_one] at h
      exact h
    have hmi : (MachineState.readWord mem 9376).toNat = minv := by
      rw [hminv, toNat_ofNat_self hminvlt]
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n - 2, by omega⟩
    exact Monpro.monproMem_represents s mem pa pb p pd a b mm hn32 hpa hpb ha hb hm hodd
      ham (by rw [hlow, hmi]; exact hminvA)
  mpFrame pa pb pd ptr v mem hptr hdisj hrep :=
    Monpro.monproMem_fastRepresents_outside s mem pa pb n pd ptr n v (by omega) hn32
      (by omega) (by omega) (by omega) hrep
  mpMinv pa pb pd mem hpd :=
    Monpro.monproMem_readWord_high s mem pa pb n pd 9376 (by omega) hn32 (by omega)
      (by omega)
  amValue pa pb pd mem a b hpa hpb hpd hm ha hb hab :=
    Csub.addmod_csub_correct mem pa pb n a b mm pd hn hn32 hpa hpb ha hb hm hmpos hab
  amFrame pa pb pd ptr v mem hptr hdisj hrep :=
    Csub.addmod_csub_preserves_region mem pa pb n pd ptr n v hn (by omega) (by omega)
      (by omega) hrep
  amMinv pa pb pd mem hpd :=
    amMemOf_readWord_high mem pa pb n pd 9376 (by omega) hn32 (by omega) (by omega)

/-- `specOf` transported onto a `Subroutines` record, so no call site ever has
to unify a projection of `subs` with a lambda. -/
theorem specOf_of {s : State} {n bsize mm minv : Nat}
    (sub : Subroutines s n bsize mm minv)
    (hmp : sub.mpMem = fun pa pb pd mem => Monpro.monproMem s mem pa pb n pd)
    (ham : sub.amMem = fun pa pb pd mem => amMemOf mem pa pb n pd)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hodd : mm % 2 = 1) (hmpos : 0 < mm)
    (hminvlt : minv < 2 ^ 256)
    (hminvA : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0) :
    SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv := by
  rw [hmp, ham]
  exact specOf s n mm minv hn hn32 hodd hmpos hminvlt hminvA

/-! ## The two `DOUBLE256` calls of the setup hand-over -/

/-- The memory a full `DOUBLE256` at `px` produces. -/
def dbl256Mem (n px : Nat) (mem : ByteArray) : ByteArray :=
  Double.iterMem (Double.dblStep px n) mem 256

/-- `Csub.fastRepresents_mcopy` in `mcopyMem` shape.  Stating it this way keeps
the unifier from ever having to `whnf` a `writeBytes` whose byte argument is a
256-fold `Double.iterMem`. -/
theorem fastRepresents_mcopyMem (mem : ByteArray) (dst src n v : Nat) (hn : 1 ≤ n)
    (hrep : Model.FastRepresents mem src n v) :
    Model.FastRepresents (mcopyMem mem dst src (32 * n)) dst n v :=
  Csub.fastRepresents_mcopy mem src dst n v hn hrep

/-- `Csub.fastRepresents_mcopy_disjoint` in `mcopyMem` shape. -/
theorem fastRepresents_mcopyMem_disjoint (mem : ByteArray) (dst src sz ptr cnt v : Nat)
    (hdisj : dst + sz ≤ ptr ∨ ptr + 32 * cnt ≤ dst)
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (mcopyMem mem dst src sz) ptr cnt v :=
  Csub.fastRepresents_mcopy_disjoint mem src dst sz ptr cnt v hdisj hrep

theorem dbl256Mem_eq (n px : Nat) (mem : ByteArray) :
    dbl256Mem n px mem = Double.iterMem (Double.dblStep px n) mem 256 := rfl

theorem dbl256Mem_frame {n bsize minv : Nat} (px : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hpx : px + 32 * n ≤ 8192) {mem : ByteArray} (hf : Frame mem n bsize minv) :
    Frame (dbl256Mem n px mem) n bsize minv := by
  have key : ∀ i, Frame (Double.iterMem (Double.dblStep px n) mem i) n bsize minv := by
    intro i
    induction i with
    | zero => exact hf
    | succ i ih => exact amMemOf_frame px px px hn hn32 hpx ih
  exact key 256

/-- One full `DOUBLE256` call, as the hand-over needs it. -/
def gasSteps_dbl256 (s : State) {n bsize minv : Nat} (esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (px : Nat) (ret : UInt256) (mem : ByteArray) (hpx : px = 4096 ∨ px = 5120)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hf : Frame mem n bsize minv) :
    Challenge.EvmProof.GasSteps (dblCall s mem px ret n bsize esize msize)
      (retTo s (dbl256Mem n px mem) ret (outer n bsize esize msize)) :=
  Double.gasSteps_double256_addmod s mem px n ret (outer n bsize esize msize)
    (by simp only [outer, List.length_cons, List.length_nil]; omega) hcode hjump hfork
    hrun hnp hact hn hn32 (by omega) (by omega) ⟨hf.s32, hf.ml, hf.tl⟩

/-! ## The guarded `R1` block

`R1B` (pc 2901) stands in front of the first `DOUBLE256` call.  When the
modulus's most significant bit is set, `radix ^ n < 2 * m`, so `R mod m` is
just `radix ^ n - m`.  `CSUB` already reduces `t[n] * radix ^ n + t_low`
against `m`, and at this point in the setup the `t` block is still zero, so
storing `t[n] := 1` turns a single `CSUB` pass into the whole of `R mod m`,
in place of the 256 modular doublings `DOUBLE256` performs.  A modulus whose
top bit is clear keeps the `DOUBLE256` path unchanged. -/

/-- The memory one `R1B` call produces. -/
def r1Mem (n px : Nat) (mem : ByteArray) : ByteArray :=
  if R1.TopBitSet mem then Csub.csResultMemory (R1.tnMem mem) n px
  else dbl256Mem n px mem

theorem readWord_tnMem_high (mem : ByteArray) (addr : Nat) (haddr : 8256 ≤ addr) :
    MachineState.readWord (R1.tnMem mem) addr = MachineState.readWord mem addr := by
  simp only [R1.tnMem]
  exact Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
    (Or.inr (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega))

theorem tnMem_readWord (mem : ByteArray) :
    MachineState.readWord (R1.tnMem mem) 8224 = UInt256.ofNat 1 := by
  simp only [R1.tnMem]
  simpa using Challenge.EvmProof.Memory.readWord_writeWord mem 8224 (UInt256.ofNat 1)

theorem tnMem_disjoint (mem : ByteArray) (ptr count value : Nat)
    (hdisj : 8224 + 32 ≤ ptr ∨ ptr + 32 * count ≤ 8224)
    (hrep : Model.FastRepresents mem ptr count value) :
    Model.FastRepresents (R1.tnMem mem) ptr count value :=
  Model.fastRepresents_writeWord_disjoint mem 8224 ptr count value 1 hdisj hrep

/-- **`R1B` leaves `R mod m` at `R1`.** -/
theorem r1Mem_represents {n mm : Nat} (hn : 2 ≤ n) (hn32 : n ≤ 32) (hmpos : 0 < mm)
    (hodd : mm % 2 = 1) (mem : ByteArray)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hr1 : Model.FastRepresents mem 4096 n (Limbs.radix ^ (n - 1)))
    (hxlt : Limbs.radix ^ (n - 1) < mm)
    (htz : Model.FastRepresents mem 8256 n 0) :
    Model.FastRepresents (r1Mem n 4096 mem) 4096 n (Limbs.radix ^ n % mm) := by
  unfold r1Mem
  split
  · rename_i htop
    have hbound : 1 * Limbs.radix ^ n + 0 < 2 * mm := by
      have h := R1.radix_pow_lt_two_mul (n := n) (mm := mm) (by omega) hodd hmod htop
      omega
    have h := Csub.csub_correct (R1.tnMem mem) n 0 mm 1 4096 hn hn32
      (tnMem_disjoint mem 8256 n 0 (Or.inl (by omega)) htz)
      (tnMem_disjoint mem 0 n mm (Or.inr (by omega)) hmod)
      (by rw [tnMem_readWord]; decide) (by omega) hmpos hbound
    simpa using h
  · have h := Double.double256_addmod_represents mem 4096 n mm (Limbs.radix ^ (n - 1))
      hn hn32 (by omega) (by omega) hmpos hmod hr1 hxlt
    have hM : Limbs.radix ^ (n - 1) * Limbs.radix = Limbs.radix ^ n := by
      rw [← pow_succ]; congr 1; omega
    rw [dbl256Mem_eq]
    rwa [hM] at h

/-- The modulus survives either branch. -/
theorem r1Mem_modulus {n mm : Nat} (hn : 2 ≤ n) (hn32 : n ≤ 32) (hmpos : 0 < mm)
    (mem : ByteArray)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hr1 : Model.FastRepresents mem 4096 n (Limbs.radix ^ (n - 1)))
    (hxlt : Limbs.radix ^ (n - 1) < mm) :
    Model.FastRepresents (r1Mem n 4096 mem) 0 n mm := by
  unfold r1Mem
  split
  · exact Csub.csub_preserves_region (R1.tnMem mem) n 4096 0 n mm hn
      (Or.inl (by omega)) (Or.inr (by omega))
      (tnMem_disjoint mem 0 n mm (Or.inr (by omega)) hmod)
  · rw [dbl256Mem_eq]
    exact Double.double256_addmod_modulus mem 4096 n mm (Limbs.radix ^ (n - 1)) hn hn32
      (by omega) (by omega) hmpos hmod hr1 hxlt

/-- Blocks strictly between the modulus and `R1` survive either branch. -/
theorem r1Mem_preserves {n ptr v : Nat} (hn : 2 ≤ n) (_hn32 : n ≤ 32)
    (_hlo : 1024 ≤ ptr) (hhi : ptr + 32 * n ≤ 4096) (mem : ByteArray)
    (hrep : Model.FastRepresents mem ptr n v) :
    Model.FastRepresents (r1Mem n 4096 mem) ptr n v := by
  unfold r1Mem
  split
  · exact Csub.csub_preserves_region (R1.tnMem mem) n 4096 ptr n v hn
      (Or.inl (by omega)) (Or.inr (by omega))
      (tnMem_disjoint mem ptr n v (Or.inr (by omega)) hrep)
  · rw [dbl256Mem_eq]
    exact Double.double256_addmod_preserves mem 4096 n ptr n v hn (Or.inl (by omega))
      (Or.inl (by omega)) (Or.inr (by omega)) hrep 256

/-- The variable block survives either branch. -/
theorem r1Mem_frame {n bsize minv : Nat} (hn : 2 ≤ n) (hn32 : n ≤ 32)
    {mem : ByteArray} (hf : Frame mem n bsize minv) :
    Frame (r1Mem n 4096 mem) n bsize minv := by
  unfold r1Mem
  split
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [Double.readWord_csResultMemory_high _ n 4096 _ (by omega) hn32 (by omega)
            (by omega),
        readWord_tnMem_high _ _ (by omega)]
      first
      | exact hf.s32 | exact hf.minvW | exact hf.ml | exact hf.tl | exact hf.eoff
  · exact dbl256Mem_frame 4096 (by omega) hn32 (by omega) hf

/-- **The guarded `R1` block against the real `CSUB`.**  Entering pc 2901 with
`[4096, ret]` returns to `ret` with `R mod m` in the block at `R1`, by one
`CSUB` pass when the modulus's top bit is set and by the 256 modular doublings
of `DOUBLE256` otherwise. -/
def gasSteps_r1Block (s : State) {n bsize minv : Nat} (esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (ret : UInt256) (mem : ByteArray)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hf : Frame mem n bsize minv) :
    Challenge.EvmProof.GasSteps (r1Call s mem 4096 ret n bsize esize msize)
      (retTo s (r1Mem n 4096 mem) ret (outer n bsize esize msize)) :=
  have hlen : (outer n bsize esize msize).length = 5 := by
    simp [outer]
  if htop : R1.TopBitSet mem then
    have hml : MachineState.readWord (R1.tnMem mem) 9408 =
        UInt256.ofNat (32 * n - 32) := by
      rw [readWord_tnMem_high _ _ (by omega)]; exact hf.ml
    have htl : MachineState.readWord (R1.tnMem mem) 9440 =
        UInt256.ofNat (8224 + 32 * n) := by
      rw [readWord_tnMem_high _ _ (by omega)]; exact hf.tl
    have hs32 : MachineState.readWord
        (Csub.csStep (R1.tnMem mem) n n).memory 9344 = UInt256.ofNat (32 * n) := by
      rw [Csub.csStep_readWord_disjoint _ n 9344 (by omega) (Or.inr (by omega)) n le_rfl,
        readWord_tnMem_high _ _ (by omega)]
      exact hf.s32
    have htn : (MachineState.readWord
        (Csub.csStep (R1.tnMem mem) n n).memory 8224).toNat ≤ 1 := by
      rw [Csub.csStep_readWord_disjoint _ n 8224 (by omega) (Or.inr (by omega)) n le_rfl,
        tnMem_readWord]
      decide
    have hdstFit : (UInt256.ofNat 4096).toNat + 32 * n ≤ 9472 := by
      rw [show (UInt256.ofNat 4096).toNat = 4096 by decide]; omega
    have g1 : Challenge.EvmProof.GasSteps
        (R1.entryState s mem 4096 ret (outer n bsize esize msize))
        (R1.fastState s mem 4096 ret (outer n bsize esize msize)) :=
      Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka blk1768 hcode hfork
        (R1.run_test_fast s mem 4096 ret (outer n bsize esize msize) (by omega)
          hcode hrun hact htop) hrun hnp
    have g2 : Challenge.EvmProof.GasSteps
        (R1.fastState s mem 4096 ret (outer n bsize esize msize))
        (R1.csubState s mem 4096 ret (outer n bsize esize msize)) :=
      Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka blk1776 hcode hfork
        (R1.run_fast s mem 4096 ret (outer n bsize esize msize) (by omega)
          hcode hrun hact) hrun hnp
    have g3 : Challenge.EvmProof.GasSteps
        (Csub.csEntryState s (R1.tnMem mem) (UInt256.ofNat 4096) ret
          (outer n bsize esize msize))
        (Csub.csReturnedState s (R1.tnMem mem) n n (UInt256.ofNat 4096) ret
          (outer n bsize esize msize)) :=
      Csub.gasSteps_csub s (R1.tnMem mem) n (UInt256.ofNat 4096) ret
        (outer n bsize esize msize) (by omega) hcode hfork hrun hnp hact hn hn32
        hjump hml htl hs32 hdstFit htn
    Challenge.EvmProof.GasSteps.cast ((g1.trans g2).trans g3) rfl
      (by simp only [Csub.csReturnedState, retTo, r1Mem, if_pos htop,
            Csub.csResultMemory, show (UInt256.ofNat 4096).toNat = 4096 by decide])
  else
    have g1 : Challenge.EvmProof.GasSteps
        (R1.entryState s mem 4096 ret (outer n bsize esize msize))
        (R1.dblState s mem 4096 ret (outer n bsize esize msize)) :=
      Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka blk1768 hcode hfork
        (R1.run_test_fallback s mem 4096 ret (outer n bsize esize msize) (by omega)
          hcode hrun hact htop) hrun hnp
    Challenge.EvmProof.GasSteps.cast
      (g1.trans (gasSteps_dbl256 s esize msize hcode hfork hrun hnp hact hn hn32 4096
        ret mem (Or.inl rfl) hjump hf))
      rfl
      (by simp only [r1Mem, if_neg htop])

/-! ## The `CCB` call of the setup hand-over

`CCB` (pc 2863) replaces the second `DOUBLE256`.  It doubles the block at
`px` once through `ADDMOD` and then squares it eight times through `MONPRO`.
`MonPro` needs only `V_MINV`, never `R1`, so it may be used here: the block
starts at `R mod m`, the Montgomery residue of `1`; doubling makes it the
residue of `2`; and eight Montgomery squarings make it the residue of
`2 ^ (2 ^ 8) = radix`, i.e. `radix * R mod m` — exactly what the 256 modular
doublings produced. -/

/-- The memory after `i` Montgomery squarings of the block at `px`. -/
def ccSqMem (mpMem : Nat → Nat → Nat → ByteArray → ByteArray) (px : Nat)
    (mem : ByteArray) : Nat → ByteArray
  | 0 => mem
  | i + 1 => mpMem px px px (ccSqMem mpMem px mem i)

theorem ccSqMem_succ (mpMem : Nat → Nat → Nat → ByteArray → ByteArray) (px : Nat)
    (mem : ByteArray) (i : Nat) :
    ccSqMem mpMem px mem (i + 1) = mpMem px px px (ccSqMem mpMem px mem i) := rfl

/-- The memory one whole `CCB` call leaves. -/
def ccbMem (mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray) (px : Nat)
    (mem : ByteArray) : ByteArray :=
  ccSqMem mpMem px (amMem px px px mem) 8

/-- The value the block at `px` holds after `i` Montgomery squarings. -/
def ccSq (mm R y : Nat) : Nat → Nat
  | 0 => y
  | i + 1 => Model.montMul mm R (ccSq mm R y i) (ccSq mm R y i)

theorem ccSq_succ (mm R y i : Nat) :
    ccSq mm R y (i + 1) = Model.montMul mm R (ccSq mm R y i) (ccSq mm R y i) := rfl

theorem ccSq_lt {mm R y : Nat} (hm : 0 < mm) (hy : y < mm) :
    ∀ i, ccSq mm R y i < mm := by
  intro i
  cases i with
  | zero => exact hy
  | succ i => exact Model.montMul_lt hm _ _ _

/-- **The `CCB` squaring invariant.**  `i` Montgomery squarings raise the
represented value to the `2 ^ i`. -/
theorem ccSq_form {mm R y c : Nat} (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    (hy : y ≡ c * R [MOD mm]) : ∀ i, ccSq mm R y i ≡ c ^ 2 ^ i * R [MOD mm] := by
  intro i
  induction i with
  | zero =>
      show ccSq mm R y 0 ≡ c ^ 2 ^ 0 * R [MOD mm]
      rw [pow_zero, pow_one]
      exact hy
  | succ i ih =>
      have hpow : c ^ 2 ^ i * c ^ 2 ^ i = c ^ 2 ^ (i + 1) := by
        rw [← pow_add, pow_succ, Nat.mul_two]
      rw [ccSq_succ, Model.montMul_form hm hcop ih ih, hpow]
      exact Nat.mod_modEq _ mm

/-- **The `CCB` postcondition.**  Doubling `R mod m` and squaring eight times
in the Montgomery domain yields `radix * R mod m`. -/
theorem ccSq_eight {mm R : Nat} (hm : 0 < mm) (hcop : Nat.Coprime R mm) :
    ccSq mm R ((R % mm + R % mm) % mm) 8 = Limbs.radix * R % mm := by
  have hy : (R % mm + R % mm) % mm ≡ 2 * R [MOD mm] := by
    calc (R % mm + R % mm) % mm
        ≡ R % mm + R % mm [MOD mm] := Nat.mod_modEq _ mm
      _ ≡ R + R [MOD mm] := Nat.ModEq.add (Nat.mod_modEq R mm) (Nat.mod_modEq R mm)
      _ = 2 * R := by ring
  have h := ccSq_form hm hcop hy 8
  have hr : (2 : Nat) ^ 2 ^ 8 = Limbs.radix := by
    show (2 : Nat) ^ 2 ^ 8 = 2 ^ 256
    norm_num
  rw [hr] at h
  have hlt : ccSq mm R ((R % mm + R % mm) % mm) 8 < mm :=
    ccSq_lt hm (Nat.mod_lt _ hm) 8
  have hmodEq : ccSq mm R ((R % mm + R % mm) % mm) 8 % mm = Limbs.radix * R % mm := h
  rwa [Nat.mod_eq_of_lt hlt] at hmodEq

/-- **The `CCB` squaring chain, at the level of memory.** -/
theorem ccSqMem_inv {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hn32 : n ≤ 32) (px : Nat) (hpxlo : 32 * n ≤ px) (hpxhi : px + 32 * n ≤ 6144)
    (mem : ByteArray) (y : Nat) (hylt : y < mm)
    (hminv : MachineState.readWord mem 9376 = UInt256.ofNat minv)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hy : Model.FastRepresents mem px n y) : ∀ i,
    Model.FastRepresents (ccSqMem mpMem px mem i) 0 n mm ∧
      MachineState.readWord (ccSqMem mpMem px mem i) 9376 = UInt256.ofNat minv ∧
      Model.FastRepresents (ccSqMem mpMem px mem i) px n (ccSq mm R y i) := by
  intro i
  induction i with
  | zero => exact ⟨hmod, hminv, hy⟩
  | succ i ih =>
      obtain ⟨hm0, hmi, hv⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · exact spec.mpFrame px px px 0 mm _ (by omega) (Or.inr (by omega)) hm0
      · exact (spec.mpMinv px px px _ (by omega)).trans hmi
      · rw [ccSqMem_succ, ccSq_succ]
        exact spec.mpValue px px px _ _ _ (by omega) (by omega) (by omega) hm0 hmi
          hv hv (ccSq_lt hm hylt i) (ccSq_lt hm hylt i)

/-- The squaring chain leaves every block disjoint from `px` alone. -/
theorem ccSqMem_preserves {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (px ptr v : Nat)
    (hptr : ptr + 32 * n ≤ 7168)
    (hdisj : px + 32 * n ≤ ptr ∨ ptr + 32 * n ≤ px) (mem : ByteArray)
    (hrep : Model.FastRepresents mem ptr n v) :
    ∀ i, Model.FastRepresents (ccSqMem mpMem px mem i) ptr n v := by
  intro i
  induction i with
  | zero => exact hrep
  | succ i ih => exact spec.mpFrame px px px ptr v _ hptr hdisj ih

/-- The squaring chain preserves the configuration words. -/
theorem ccSqMem_frame {s : State} {n bsize mm minv : Nat}
    (sub : Subroutines s n bsize mm minv) (px : Nat) (hpx : px ≤ 6144)
    (mem : ByteArray) (hf : Frame mem n bsize minv) :
    ∀ i, Frame (ccSqMem sub.mpMem px mem i) n bsize minv := by
  intro i
  induction i with
  | zero => exact hf
  | succ i ih => exact sub.mpFrame px px px _ hpx ih

theorem ccbMem_frame {s : State} {n bsize mm minv : Nat}
    (sub : Subroutines s n bsize mm minv) (px : Nat) (hpx : px ≤ 6144)
    (mem : ByteArray) (hf : Frame mem n bsize minv) :
    Frame (ccbMem sub.mpMem sub.amMem px mem) n bsize minv :=
  ccSqMem_frame sub px hpx _ (sub.amFrame px px px mem hpx hf) 8

theorem ccbMem_preserves {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (px ptr v : Nat)
    (hptr : ptr + 32 * n ≤ 7168)
    (hdisj : px + 32 * n ≤ ptr ∨ ptr + 32 * n ≤ px) (mem : ByteArray)
    (hrep : Model.FastRepresents mem ptr n v) :
    Model.FastRepresents (ccbMem mpMem amMem px mem) ptr n v :=
  ccSqMem_preserves spec px ptr v hptr hdisj _
    (spec.amFrame px px px ptr v mem hptr hdisj hrep) 8

/-- **The `CCB` postcondition, at the level of memory.** -/
theorem ccbMem_represents {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hcop : Nat.Coprime R mm) (hn32 : n ≤ 32) (px : Nat) (hpxlo : 32 * n ≤ px)
    (hpxhi : px + 32 * n ≤ 6144) (mem : ByteArray)
    (hminv : MachineState.readWord mem 9376 = UInt256.ofNat minv)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hy : Model.FastRepresents mem px n (R % mm)) :
    Model.FastRepresents (ccbMem mpMem amMem px mem) px n (Limbs.radix * R % mm) := by
  have ham : Model.FastRepresents (amMem px px px mem) px n ((R % mm + R % mm) % mm) :=
    spec.amValue px px px mem (R % mm) (R % mm) (by omega) (by omega) (by omega)
      hmod hy hy (by have := Nat.mod_lt R hm; omega)
  have hmod' : Model.FastRepresents (amMem px px px mem) 0 n mm :=
    spec.amFrame px px px 0 mm mem (by omega) (Or.inr (by omega)) hmod
  have hminv' : MachineState.readWord (amMem px px px mem) 9376 =
      UInt256.ofNat minv := (spec.amMinv px px px mem (by omega)).trans hminv
  have h := (ccSqMem_inv spec hm hn32 px hpxlo hpxhi (amMem px px px mem)
    ((R % mm + R % mm) % mm) (Nat.mod_lt _ hm) hminv' hmod' ham 8).2.2
  rwa [ccSq_eight hm hcop] at h

/-- The modulus block survives a whole `CCB` call. -/
theorem ccbMem_modulus {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hn32 : n ≤ 32)
    (px : Nat) (hpxlo : 32 * n ≤ px) (_hpxhi : px + 32 * n ≤ 6144) (mem : ByteArray)
    (hmod : Model.FastRepresents mem 0 n mm) :
    Model.FastRepresents (ccbMem mpMem amMem px mem) 0 n mm :=
  ccbMem_preserves spec px 0 mm (by omega) (Or.inr (by omega)) mem hmod

theorem jump2874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat 2874).toNat = true := by
  rw [show (UInt256.ofNat 2874).toNat = 2874 by decide]
  exact jumpDest2874

theorem jump2888 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat 2888).toNat = true := by
  rw [show (UInt256.ofNat 2888).toNat = 2888 by decide]
  exact jumpDest2888

/-- **`CCB` against the real `ADDMOD` and `MONPRO`.**  Entering pc 2863 with
`[px, ret] ++ OUTER` returns to `ret` with the block at `px` multiplied by
`radix` modulo `m`. -/
def gasSteps_ccbFull (s : State) {n bsize mm minv R : Nat}
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm R minv)
    (esize msize : Nat) (hm : 0 < mm) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (px : Nat) (hpxlo : 32 * n ≤ px) (hpxhi : px + 32 * n ≤ 6144)
    (ret : UInt256) (mem : ByteArray) (y : Nat)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hf : Frame mem n bsize minv)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hy : Model.FastRepresents mem px n y) (hylt : y < mm)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (ccCall s mem px ret n bsize esize msize)
      (retTo s (ccbMem sub.mpMem sub.amMem px mem) ret (outer n bsize esize msize)) :=
  have hpx6 : px ≤ 6144 := by omega
  have hmod' : Model.FastRepresents (sub.amMem px px px mem) 0 n mm :=
    spec.amFrame px px px 0 mm mem (by omega) (Or.inr (by omega)) hmod
  have hminv' : MachineState.readWord (sub.amMem px px px mem) 9376 =
      UInt256.ofNat minv := (spec.amMinv px px px mem hpx6).trans hf.minvW
  have ham : Model.FastRepresents (sub.amMem px px px mem) px n ((y + y) % mm) :=
    spec.amValue px px px mem y y (by omega) (by omega) (by omega) hmod hy hy
      (by omega)
  have hframe' : Frame (sub.amMem px px px mem) n bsize minv :=
    sub.amFrame px px px mem hpx6 hf
  Ccb.gasSteps_ccb s px ret (outer n bsize esize msize) mem
    (ccSqMem sub.mpMem px (sub.amMem px px px mem))
    (sub.addmod px px px (UInt256.ofNat 2874)
      ([UInt256.ofNat px, ret] ++ outer n bsize esize msize) mem
      (by simp only [outer, List.length_cons, List.length_nil,
        List.length_append]; omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) jump2874 hf)
    (fun i hi =>
      sub.monpro px px px (UInt256.ofNat 2888)
        (Ccb.loopStack px (8 - i) ret (outer n bsize esize msize))
        (ccSqMem sub.mpMem px (sub.amMem px px px mem) i)
        (ccSq mm R ((y + y) % mm) i) (ccSq mm R ((y + y) % mm) i)
        (by simp only [Ccb.loopStack, outer, List.length_cons, List.length_nil,
          List.length_append]; omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) jump2888
        (ccSqMem_frame sub px hpx6 _ hframe' i)
        (ccSqMem_inv spec hm hn32 px hpxlo hpxhi _ ((y + y) % mm)
          (Nat.mod_lt _ hm) hminv' hmod' ham i).1
        (ccSqMem_inv spec hm hn32 px hpxlo hpxhi _ ((y + y) % mm)
          (Nat.mod_lt _ hm) hminv' hmod' ham i).2.2
        (ccSqMem_inv spec hm hn32 px hpxlo hpxhi _ ((y + y) % mm)
          (Nat.mod_lt _ hm) hminv' hmod' ham i).2.2
        (ccSq_lt hm (Nat.mod_lt _ hm) i))
    (by simp only [outer, List.length_cons, List.length_nil]; omega)
    hcode hjump hfork hrun hnp

/-- The modulus block and the `CC` block as the `CCB` call finds them: the
`DOUBLE256` chain has turned `R1` into `R mod m` and the `MCOPY` has copied it
to `CC`. -/
theorem setupToCC_facts (n mm : Nat) (hn : 2 ≤ n) (hn32 : n ≤ 32) (hmpos : 0 < mm)
    (hodd : mm % 2 = 1)
    (mem : ByteArray) (hmod : Model.FastRepresents mem 0 n mm)
    (hr1 : Model.FastRepresents mem 4096 n (Limbs.radix ^ (n - 1)))
    (hxlt : Limbs.radix ^ (n - 1) < mm)
    (htz : Model.FastRepresents mem 8256 n 0) :
    Model.FastRepresents (mcopyMem (r1Mem n 4096 mem) 5120 4096 (32 * n)) 0 n mm ∧
      Model.FastRepresents (mcopyMem (r1Mem n 4096 mem) 5120 4096 (32 * n)) 5120 n
        (Limbs.radix ^ n % mm) := by
  have hM : Limbs.radix ^ (n - 1) * Limbs.radix = Limbs.radix ^ n := by
    rw [← pow_succ]; congr 1; omega
  have h1r : Model.FastRepresents (r1Mem n 4096 mem) 4096 n
      (Limbs.radix ^ n % mm) :=
    r1Mem_represents hn hn32 hmpos hodd mem hmod hr1 hxlt htz
  have h1m : Model.FastRepresents (r1Mem n 4096 mem) 0 n mm :=
    r1Mem_modulus hn hn32 hmpos mem hmod hr1 hxlt
  exact ⟨fastRepresents_mcopyMem_disjoint (r1Mem n 4096 mem) 5120 4096 (32 * n)
      0 n mm (by omega) h1m,
    fastRepresents_mcopyMem (r1Mem n 4096 mem) 5120 4096 n (Limbs.radix ^ n % mm)
      (by omega) h1r⟩

theorem setupToRR_frame {s : State} {n bsize mm minv : Nat}
    (sub : Subroutines s n bsize mm minv) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    {mem : ByteArray} (hf : Frame mem n bsize minv) :
    Frame (setupToRRMem (r1Mem n) (ccbMem sub.mpMem sub.amMem) n mem)
      n bsize minv :=
  frame_mcopyMem (by omega)
    (ccbMem_frame sub 5120 (by omega) _
      (frame_mcopyMem (by omega) (r1Mem_frame (by omega) hn32 hf)))

theorem setupToRR_preserves {s : State} {n bsize mm minv R : Nat}
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm R minv)
    (ptr v : Nat) (hn : 2 ≤ n) (_hn32 : n ≤ 32)
    (_hlo : 1024 ≤ ptr) (hhi : ptr + 32 * n ≤ 4096) (mem : ByteArray)
    (hrep : Model.FastRepresents mem ptr n v) :
    Model.FastRepresents
      (setupToRRMem (r1Mem n) (ccbMem sub.mpMem sub.amMem) n mem) ptr n v := by
  have h1 : Model.FastRepresents (r1Mem n 4096 mem) ptr n v :=
    r1Mem_preserves hn _hn32 _hlo hhi mem hrep
  have h2 : Model.FastRepresents (mcopyMem (r1Mem n 4096 mem) 5120 4096 (32 * n))
      ptr n v :=
    fastRepresents_mcopyMem_disjoint (r1Mem n 4096 mem) 5120 4096 (32 * n) ptr n v
      (by omega) h1
  have h3 : Model.FastRepresents
      (ccbMem sub.mpMem sub.amMem 5120
        (mcopyMem (r1Mem n 4096 mem) 5120 4096 (32 * n))) ptr n v :=
    ccbMem_preserves spec 5120 ptr v (by omega) (Or.inr (by omega)) _ h2
  exact fastRepresents_mcopyMem_disjoint
    (ccbMem sub.mpMem sub.amMem 5120
      (mcopyMem (r1Mem n 4096 mem) 5120 4096 (32 * n)))
    6144 4096 (32 * n) ptr n v (by omega) h3

/-- The two `DOUBLE256` calls and the two `MCOPY`s of the hand-over turn the
setup's `R1 = radix ^ (n - 1)` into the `RR`-loop invariant. -/
theorem setupToRR_inv {s : State} {bsize minv : Nat} (n mm : Nat)
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hmpos : 0 < mm) (hodd : mm % 2 = 1)
    (mem : ByteArray) (hframe : Frame mem n bsize minv)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hr1 : Model.FastRepresents mem 4096 n (Limbs.radix ^ (n - 1)))
    (hxlt : Limbs.radix ^ (n - 1) < mm)
    (htz : Model.FastRepresents mem 8256 n 0) :
    RrInv (setupToRRMem (r1Mem n) (ccbMem sub.mpMem sub.amMem) n mem) n mm
      (Limbs.radix ^ n) (Limbs.radix ^ n % mm) := by
  have hcop : Nat.Coprime (Limbs.radix ^ n) mm := Model.coprime_radix_pow_of_odd hodd n
  have hf1 : Frame (r1Mem n 4096 mem) n bsize minv :=
    r1Mem_frame (by omega) hn32 hframe
  have hf2 : Frame (mcopyMem (r1Mem n 4096 mem) 5120 4096 (32 * n)) n bsize minv :=
    frame_mcopyMem (by omega) hf1
  have hM : Limbs.radix ^ (n - 1) * Limbs.radix = Limbs.radix ^ n := by
    rw [← pow_succ]; congr 1; omega
  have h1r : Model.FastRepresents (r1Mem n 4096 mem) 4096 n
      (Limbs.radix ^ n % mm) :=
    r1Mem_represents hn hn32 hmpos hodd mem hmod hr1 hxlt htz
  have h1m : Model.FastRepresents (r1Mem n 4096 mem) 0 n mm :=
    r1Mem_modulus hn hn32 hmpos mem hmod hr1 hxlt
  have h2c : Model.FastRepresents (mcopyMem (r1Mem n 4096 mem) 5120 4096 (32 * n))
      5120 n (Limbs.radix ^ n % mm) :=
    fastRepresents_mcopyMem (r1Mem n 4096 mem) 5120 4096 n (Limbs.radix ^ n % mm)
      (by omega) h1r
  have h2r : Model.FastRepresents (mcopyMem (r1Mem n 4096 mem) 5120 4096 (32 * n))
      4096 n (Limbs.radix ^ n % mm) :=
    fastRepresents_mcopyMem_disjoint (r1Mem n 4096 mem) 5120 4096 (32 * n) 4096 n
      (Limbs.radix ^ n % mm) (by omega) h1r
  have h2m : Model.FastRepresents (mcopyMem (r1Mem n 4096 mem) 5120 4096 (32 * n))
      0 n mm :=
    fastRepresents_mcopyMem_disjoint (r1Mem n 4096 mem) 5120 4096 (32 * n) 0 n mm
      (by omega) h1m
  have h3c : Model.FastRepresents
      (ccbMem sub.mpMem sub.amMem 5120
        (mcopyMem (r1Mem n 4096 mem) 5120 4096 (32 * n))) 5120 n
      (Limbs.radix * Limbs.radix ^ n % mm) :=
    ccbMem_represents spec hmpos hcop hn32 5120 (by omega) (by omega) _ hf2.minvW
      h2m h2c
  have h3m : Model.FastRepresents
      (ccbMem sub.mpMem sub.amMem 5120
        (mcopyMem (r1Mem n 4096 mem) 5120 4096 (32 * n))) 0 n mm :=
    ccbMem_modulus spec hn32 5120 (by omega) (by omega) _ h2m
  have h3r : Model.FastRepresents
      (ccbMem sub.mpMem sub.amMem 5120
        (mcopyMem (r1Mem n 4096 mem) 5120 4096 (32 * n))) 4096 n
      (Limbs.radix ^ n % mm) :=
    ccbMem_preserves spec 5120 4096 (Limbs.radix ^ n % mm) (by omega)
      (Or.inr (by omega)) _ h2r
  exact ⟨fastRepresents_mcopyMem_disjoint
      (ccbMem sub.mpMem sub.amMem 5120
        (mcopyMem (r1Mem n 4096 mem) 5120 4096 (32 * n)))
      6144 4096 (32 * n) 0 n mm (by omega) h3m,
    fastRepresents_mcopyMem_disjoint
      (ccbMem sub.mpMem sub.amMem 5120
        (mcopyMem (r1Mem n 4096 mem) 5120 4096 (32 * n)))
      6144 4096 (32 * n) 4096 n (Limbs.radix ^ n % mm) (by omega) h3r,
    fastRepresents_mcopyMem_disjoint
      (ccbMem sub.mpMem sub.amMem 5120
        (mcopyMem (r1Mem n 4096 mem) 5120 4096 (32 * n)))
      6144 4096 (32 * n) 5120 n (Limbs.radix * Limbs.radix ^ n % mm) (by omega) h3c,
    fastRepresents_mcopyMem
      (ccbMem sub.mpMem sub.amMem 5120
        (mcopyMem (r1Mem n 4096 mem) 5120 4096 (32 * n)))
      6144 4096 n (Limbs.radix ^ n % mm) (by omega) h3r⟩

/-! ## The setup memory outside the modulus and `R1` blocks -/

/-- Nothing the setup block writes lands between `0x0400` and `0x1000`. -/
theorem readWord_setupMem_mid (input : ByteArray) (m0 target : Nat)
    (hm : Challenge.Modexp.modulusSize input ≤ 1024)
    (hlo : 1024 ≤ target) (hhi : target + 32 ≤ 4096) :
    MachineState.readWord (Setup.setupMem ByteArray.empty input m0) target =
      UInt256.ofNat 0 := by
  have hS := Setup.s32_le_1024 input hm
  have hms := Setup.modulusSize_le_s32 input
  unfold Setup.setupMem Setup.modulusMem Setup.varsMem
  rw [Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_writeBytes_ne _ _ _ _
      (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    Setup.readWord_writeBytes_ne _ _ _ _
      (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_empty]

/-- `ACC`, `BASE` and the `ONE` slot are all zero when the setup hands over. -/
theorem fastSetup_zero_block (input : ByteArray) (hpath : Setup.FastPath input)
    (ptr : Nat) (hlo : 1024 ≤ ptr) (hhi : ptr + 32 * Setup.limbs input ≤ 4096) :
    Model.FastRepresents (Setup.fastSetupMemory input) ptr (Setup.limbs input) 0 := by
  rw [Model.fastRepresents_zero_iff]
  intro j hj
  rw [Setup.fastSetupMemory,
    readWord_setupMem_mid input (Setup.lowLimb input) (ptr + 32 * j) hpath.2.1.2.2
      (by omega) (by omega),
    toNat_ofNat_self (by norm_num)]

/-- Nothing the setup block writes lands between `0x1020` and the variables. -/
theorem readWord_setupMem_high (input : ByteArray) (m0 target : Nat)
    (hm : Challenge.Modexp.modulusSize input ≤ 1024)
    (hlo : 4128 ≤ target) (hhi : target + 32 ≤ 9344) :
    MachineState.readWord (Setup.setupMem ByteArray.empty input m0) target =
      UInt256.ofNat 0 := by
  have hS := Setup.s32_le_1024 input hm
  have hms := Setup.modulusSize_le_s32 input
  unfold Setup.setupMem Setup.modulusMem Setup.varsMem
  rw [Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inr (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_writeBytes_ne _ _ _ _
      (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    Setup.readWord_writeBytes_ne _ _ _ _
      (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_empty]

/-- The CIOS `t` block is still zero when the setup hands over, which is what
lets `CSUB` compute `radix ^ n - m` from `t[n] = 1` alone. -/
theorem fastSetup_tblock_zero (input : ByteArray) (hpath : Setup.FastPath input)
    (hn32 : Setup.limbs input ≤ 32) :
    Model.FastRepresents (Setup.fastSetupMemory input) 8256 (Setup.limbs input) 0 := by
  rw [Model.fastRepresents_zero_iff]
  intro j hj
  rw [Setup.fastSetupMemory,
    readWord_setupMem_high input (Setup.lowLimb input) (8256 + 32 * j) hpath.2.1.2.2
      (by omega) (by omega),
    toNat_ofNat_self (by norm_num)]

/-! ## The hand-over state, field by field -/

theorem fastSetup_code (input : ByteArray) :
    (Setup.fastSetupState input).executionEnv.code =
      Challenge.Modexp.submissionBytecode := rfl

theorem fastSetup_fork (input : ByteArray) :
    (Setup.fastSetupState input).fork = .Osaka := rfl

theorem fastSetup_halt (input : ByteArray) :
    (Setup.fastSetupState input).halt = .Running := rfl

theorem fastSetup_calldata (input : ByteArray) :
    (Setup.fastSetupState input).executionEnv.calldata = input := rfl

theorem fastSetup_callStack (input : ByteArray) :
    (Setup.fastSetupState input).callStack = [] := rfl

theorem fastSetup_notPrecompile (input : ByteArray) :
    Precompile.isPrecompileWithConfig
      (Setup.fastSetupState input).executionEnv.precompileConfig
      (Setup.fastSetupState input).executionEnv.fork
      (Setup.fastSetupState input).executionEnv.codeAddr = false :=
  Challenge.Modexp.deployAddress_not_precompile

/-- The hand-over state is the entry state of the `R1B` guard. -/
theorem fastSetup_entry_eq (input : ByteArray) :
    Setup.fastSetupState input =
      r1Call (Setup.fastSetupState input) (Setup.fastSetupMemory input) 4096
        (UInt256.ofNat 1533) (Setup.limbs input) (Challenge.Modexp.baseSize input)
        (Challenge.Modexp.exponentSize input) (Challenge.Modexp.modulusSize input) := rfl

/-! ## The top-level certificate -/

/-- The two memory transformers of `subs`, read off by `iota` rather than by
unification: `unfold` turns the projection into a projection *of a
constructor*, which `whnfCore` reduces without ever unfolding
`Monpro.monproMem` into its `writeBytes` / `rowsMem` recursion. -/
theorem subs_mpMem (s : State) (n bsize mm minv : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hmpos : 0 < mm) (hminvlt : minv < 2 ^ 256)
    (hminvA : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0) :
    (subs s n bsize mm minv hcode hfork hrun hnp hact hcds hn hn32 hmpos
      hminvlt hminvA).mpMem =
      fun pa pb pd mem => Monpro.monproMem s mem pa pb n pd := by
  delta subs
  rfl

theorem subs_amMem (s : State) (n bsize mm minv : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hmpos : 0 < mm) (hminvlt : minv < 2 ^ 256)
    (hminvA : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0) :
    (subs s n bsize mm minv hcode hfork hrun hnp hact hcds hn hn32 hmpos
      hminvlt hminvA).amMem =
      fun pa pb pd mem => amMemOf mem pa pb n pd := by
  delta subs
  rfl

/-- The value contract of the concrete instance, at the concrete instance. -/
theorem specOf_subs (s : State) (n bsize mm minv : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hmpos : 0 < mm) (hminvlt : minv < 2 ^ 256)
    (hminvA : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0) (hodd : mm % 2 = 1) :
    SubSpec (subs s n bsize mm minv hcode hfork hrun hnp hact hcds hn hn32 hmpos
        hminvlt hminvA).mpMem
      (subs s n bsize mm minv hcode hfork hrun hnp hact hcds hn hn32 hmpos hminvlt
        hminvA).amMem n mm (Limbs.radix ^ n) minv :=
  specOf_of (subs s n bsize mm minv hcode hfork hrun hnp hact hcds hn hn32 hmpos
    hminvlt hminvA)
    (subs_mpMem s n bsize mm minv hcode hfork hrun hnp hact hcds hn hn32 hmpos hminvlt
      hminvA)
    (subs_amMem s n bsize mm minv hcode hfork hrun hnp hact hcds hn hn32 hmpos hminvlt
      hminvA)
    hn hn32 hodd hmpos hminvlt hminvA

/-- The hand-over: two `DOUBLE256` calls and two `MCOPY`s. -/
def gasSteps_handover (s : State) (mem : ByteArray) (n bsize esize msize mm minv : Nat)
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 298 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32) (hmpos : 0 < mm)
    (hodd : mm % 2 = 1)
    (hmod0 : Model.FastRepresents mem 0 n mm)
    (hr10 : Model.FastRepresents mem 4096 n (Limbs.radix ^ (n - 1)))
    (hxlt : Limbs.radix ^ (n - 1) < mm)
    (htz : Model.FastRepresents mem 8256 n 0)
    (hframe0 : Frame mem n bsize minv) :
    Challenge.EvmProof.GasSteps
      (r1Call s mem 4096 (UInt256.ofNat 1533) n bsize esize msize)
      (rrHead s (setupToRRMem (r1Mem n) (ccbMem sub.mpMem sub.amMem) n mem)
        n bsize esize msize 5) :=
  gasSteps_setupToRR s sub mem esize msize (r1Mem n) (ccbMem sub.mpMem sub.amMem)
    (fun ret mem' hjump hf =>
      gasSteps_r1Block s esize msize hcode hfork hrun hnp
        (Nat.le_trans (show 296 ≤ 298 by norm_num) hact) hn hn32 ret mem' hjump hf)
    (fun ret mem' y' hjump hf hmod' hy' hylt' =>
      gasSteps_ccbFull s sub spec esize msize hmpos hn hn32 5120 (by omega) (by omega)
        ret mem' y' hjump hf hmod' hy' hylt' hcode hfork hrun hnp)
    (fun mem' hf => r1Mem_frame (by omega) hn32 hf)
    (fun mem' hf => ccbMem_frame sub 5120 (by omega) mem' hf)
    (Limbs.radix ^ n % mm)
    (setupToCC_facts n mm hn hn32 hmpos hodd mem hmod0 hr10 hxlt htz).1
    (setupToCC_facts n mm hn hn32 hmpos hodd mem hmod0 hr10 hxlt htz).2
    (Nat.mod_lt _ hmpos)
    hn hn32 hact hframe0 hcode hfork hrun hnp

/-- Everything after `Fast.Setup`: the hand-over, the three loops and the
`RETURN`.  Stated over an abstract hand-over state so that every `subs`
projection is a projection at variables. -/
theorem handled_of_handover (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize mm minv : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hdata : s.executionEnv.calldata = input) (hstack : s.callStack = [])
    (hact : 298 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (hmz : 32 < msize) (hm32 : msize ≤ 32 * n)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hmm : mm = Precompile.bytesToNatPadded input (96 + bsize + esize) msize)
    (hodd : mm % 2 = 1) (hradix : Limbs.radix ≤ mm) (hmpos : 0 < mm)
    (hminvlt : minv < 2 ^ 256)
    (hminvA : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0)
    (hxlt : Limbs.radix ^ (n - 1) < mm)
    (hframe0 : Frame mem n bsize minv)
    (hmod0 : Model.FastRepresents mem 0 n mm)
    (hr10 : Model.FastRepresents mem 4096 n (Limbs.radix ^ (n - 1)))
    (hacc0 : Model.FastRepresents mem 1024 n 0)
    (hbase0 : Model.FastRepresents mem 2048 n 0)
    (hone0 : Model.FastRepresents mem 3072 n 0)
    (htz : Model.FastRepresents mem 8256 n 0) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps
        (r1Call s mem 4096 (UInt256.ofNat 1533) n bsize esize msize) final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) := by
  have hact296 : 296 ≤ s.activeWords.toNat :=
    Nat.le_trans (show 296 ≤ 298 by norm_num) hact
  obtain ⟨final, ⟨tr⟩, hdone, hres⟩ :=
    handled_of_rrHead input s
      (setupToRRMem (r1Mem n)
        (ccbMem (subs s n bsize mm minv hcode hfork hrun hnp hact296 hcds hn hn32 hmpos
      hminvlt hminvA).mpMem
          (subs s n bsize mm minv hcode hfork hrun hnp hact296 hcds hn hn32 hmpos
      hminvlt hminvA).amMem) n mem)
      n bsize esize msize mm
      minv (subs s n bsize mm minv hcode hfork hrun hnp hact296 hcds hn hn32 hmpos
      hminvlt hminvA)
      (specOf_subs s n bsize mm minv hcode hfork hrun hnp hact296 hcds hn hn32 hmpos
      hminvlt hminvA hodd)
      hcode hfork hrun hnp hdata hstack hact hn hn32 hb he hmz hm32 hbsize hesize hmsz
      hmm hodd hradix
      (setupToRR_frame (subs s n bsize mm minv hcode hfork hrun hnp hact296 hcds hn hn32 hmpos
      hminvlt hminvA) hn hn32 hframe0)
      (setupToRR_inv n mm (subs s n bsize mm minv hcode hfork hrun hnp hact296 hcds hn hn32 hmpos
      hminvlt hminvA)
        (specOf_subs s n bsize mm minv hcode hfork hrun hnp hact296 hcds hn hn32 hmpos
      hminvlt hminvA hodd)
        hn hn32 hmpos hodd mem hframe0 hmod0 hr10 hxlt htz)
      (setupToRR_preserves (subs s n bsize mm minv hcode hfork hrun hnp hact296 hcds hn hn32 hmpos
      hminvlt hminvA)
        (specOf_subs s n bsize mm minv hcode hfork hrun hnp hact296 hcds hn hn32 hmpos
      hminvlt hminvA hodd)
        1024 0 hn hn32 (by omega) (by omega) mem hacc0)
      (setupToRR_preserves (subs s n bsize mm minv hcode hfork hrun hnp hact296 hcds hn hn32 hmpos
      hminvlt hminvA)
        (specOf_subs s n bsize mm minv hcode hfork hrun hnp hact296 hcds hn hn32 hmpos
      hminvlt hminvA hodd)
        2048 0 hn hn32 (by omega) (by omega) mem hbase0)
      (setupToRR_preserves (subs s n bsize mm minv hcode hfork hrun hnp hact296 hcds hn hn32 hmpos
      hminvlt hminvA)
        (specOf_subs s n bsize mm minv hcode hfork hrun hnp hact296 hcds hn hn32 hmpos
      hminvlt hminvA hodd)
        3072 0 hn hn32 (by omega) (by omega) mem hone0)
  exact ⟨final, ⟨(gasSteps_handover s mem n bsize esize msize mm minv
    (subs s n bsize mm minv hcode hfork hrun hnp hact296 hcds hn hn32 hmpos
      hminvlt hminvA)
    (specOf_subs s n bsize mm minv hcode hfork hrun hnp hact296 hcds hn hn32 hmpos
      hminvlt hminvA hodd)
    hcode hfork hrun hnp hact hn hn32 hmpos hodd hmod0 hr10 hxlt htz
    hframe0).trans tr⟩,
    hdone, hres⟩

/-- **Fast-path certificate.**  Every `ValidInput` on the fast path runs from
the retargeted entry to a `RETURN` whose payload is the MODEXP specification. -/
theorem gasSteps_handled (input : ByteArray)
    (hvalid : Challenge.Modexp.ValidInput input)
    (hpath : Challenge.Modexp.Submission.Proofs.Fast.Setup.FastPath input) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps
        (Main.trampolineState input 1314) final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) := by
  have hsize : input.size < 2 ^ 256 := lt_trans hvalid.1 (by norm_num)
  have hn : 2 ≤ Setup.limbs input := Setup.limbs_ge_two input hpath.1
  have hn32 : Setup.limbs input ≤ 32 := Setup.fastSetup_limbs_le_32 input hpath
  have hodd : Setup.modulus input % 2 = 1 := hpath.2.2.2
  have hradix : Limbs.radix ≤ Setup.modulus input := by
    have h1 : Limbs.radix ^ 1 ≤ Limbs.radix ^ (Setup.limbs input - 1) :=
      Nat.pow_le_pow_right (le_of_lt Limbs.radix_gt_one) (by omega)
    have h2 := hpath.2.2.1
    rw [pow_one] at h1
    omega
  have hmpos : 0 < Setup.modulus input := lt_of_lt_of_le Limbs.radix_pos hradix
  have hminvlt : Setup.minvValue input < 2 ^ 256 := Setup.negWord_lt _
  have hminvA : (Setup.modulus input % Limbs.radix * Setup.minvValue input + 1)
      % 2 ^ 256 = 0 := by
    have h := Setup.fastSetup_minv input hpath
    rw [Setup.fastSetup_lowLimb input hpath] at h
    exact h
  have hxlt : Limbs.radix ^ (Setup.limbs input - 1) < Setup.modulus input :=
    Model.radix_pow_lt_of_odd hn hpath.2.2.1 hodd
  have hact : 298 ≤ (Setup.fastSetupState input).activeWords.toNat := by
    rw [Setup.fastSetup_activeWords input hpath, toNat_ofNat_self (by norm_num)]
  have hcds : (Setup.fastSetupState input).executionEnv.calldata.size < 2 ^ 256 := by
    rw [fastSetup_calldata input]; exact hsize
  obtain ⟨final, ⟨tr⟩, hdone, hres⟩ :=
    handled_of_handover input (Setup.fastSetupState input) (Setup.fastSetupMemory input)
      (Setup.limbs input) (Challenge.Modexp.baseSize input)
      (Challenge.Modexp.exponentSize input) (Challenge.Modexp.modulusSize input)
      (Setup.modulus input) (Setup.minvValue input)
      (fastSetup_code input) (fastSetup_fork input) (fastSetup_halt input)
      (fastSetup_notPrecompile input) (fastSetup_calldata input)
      (fastSetup_callStack input) hact hcds hn hn32 hpath.2.1.1 hpath.2.1.2.1 hpath.1
      (Setup.modulusSize_le_s32 input) rfl rfl rfl (Setup.fastSetup_modulus_eq input)
      hodd hradix hmpos hminvlt hminvA hxlt
      ⟨Setup.fastSetup_V_S32 input hpath, Setup.fastSetup_V_MINV input,
       Setup.fastSetup_V_ML input hpath, Setup.fastSetup_V_TL input hpath,
       Setup.fastSetup_V_EOFF input hpath⟩
      (Setup.fastSetup_modulus input hpath) (Setup.fastSetup_R1 input hpath)
      (fastSetup_zero_block input hpath 1024 (by omega) (by omega))
      (fastSetup_zero_block input hpath 2048 (by omega) (by omega))
      (fastSetup_zero_block input hpath 3072 (by omega) (by omega))
      (fastSetup_tblock_zero input hpath hn32)
  exact ⟨final, ⟨(Challenge.EvmProof.GasSteps.cast
    (Setup.gasSteps_fastSetup input hsize hpath) rfl (fastSetup_entry_eq input)).trans
    tr⟩, hdone, hres⟩

#print axioms gasSteps_handled


end Challenge.Modexp.Submission.Proofs.Fast.Exp
