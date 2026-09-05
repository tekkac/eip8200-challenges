import Challenge.Ripemd160.Spec
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Word
import Challenge.Ripemd160.Submission.Proofs.Bytecode.FastEmptyBlock
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SpecBridge

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.EmptyFastSpec

open Challenge.Ripemd160
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM Crypto

def emptyPaddedDigest : ByteArray := ByteArray.mk #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0x9c, 0x11, 0x85, 0xa5, 0xc5, 0xe9, 0xfc, 0x54,
  0x61, 0x28, 0x08, 0x97, 0x7e, 0xe8, 0xf5, 0x48,
  0xb2, 0x25, 0x8d, 0x31
]

def emptyDigestWord : UInt256 :=
  UInt256.ofNat 0x0000000000000000000000009c1185a5c5e9fc54612808977ee8f548b2258d31

theorem spec_empty_eq : spec ByteArray.empty = emptyPaddedDigest := by
  unfold spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  rw [← HashSpecBridge.paddedHash_eq_hash]
  change (ByteArray.mk #[0,0,0,0,0,0,0,0,0,0,0,0]) ++
    SpecBridge.emitDigest (SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage ByteArray.empty) 0 1) = _
  rw [SpecBridge.absorbBlocks_succ, SpecBridge.absorbBlocks_zero]
  norm_num
  rw [FastEmptyBlock.compress_empty]
  unfold SpecBridge.emitDigest emptyPaddedDigest
  norm_num [List.range, List.range.loop]
  unfold Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  decide

theorem wordBytes_eq_emptyPaddedDigest :
    Data.Bytes.natToBytesPadded emptyDigestWord.toNat 32 = emptyPaddedDigest := by
  rw [Challenge.EvmProof.Memory.natToBytesPadded_eq_natToBE]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.EmptyFastSpec
