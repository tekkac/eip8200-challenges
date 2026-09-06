import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailConsume
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# Cached-factor consume-tail raw trace

Retires the old DUP/POP tail evaluator. The consume body is the frozen
53-instruction sequence through the earlier `JUMP`; nine `STOP` bytes are
not executed.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailTrace

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailConsume

theorem runTail_quadTail
    (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256)
    (hactive : 66 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1007)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    StackTail.runTailInstrs quadTailTemplate
      (tailEntry s left right ret rest) =
      some (finalResult s left right ret rest) := by
  simpa [quadTailTemplate] using
    runTail_consumeBody s left right ret rest hactive hstack hvalid

theorem runInstrSeq_quadTail
    (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256)
    (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka)
    (hactive : 66 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1007)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    QuadTailConsume.runInstrSeq consumeBody
      (tailEntry s left right ret rest) =
      some (finalResult s left right ret rest) :=
  run_consumeBody s left right ret rest hrun hfork hactive hstack hvalid

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailTrace
