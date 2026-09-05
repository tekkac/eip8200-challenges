import Challenge.Modexp.Submission.Proofs.Memo.Dispatch
import Challenge.Modexp.Submission.Proofs.Memo.V2.Data

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.V2.State

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Memo
open Logic

def earlyJumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1480
      stack := [UInt256.ofNat 1553, MachineState.readWord input 32] }

def accState (input : ByteArray) (pc : Nat) (acc : UInt256) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat pc
      stack := [acc] }

def remainingChecks : List (Nat × UInt256) :=
  [(0, 1),
   (64, 1),
   (96, 19168523805780691591649194585559922978212372797203590076661305677823631949824)]

def accRest (input : ByteArray) : UInt256 :=
  guardDiff remainingChecks input

theorem guardDiff_split (input : ByteArray) :
    guardDiff Data.checks input = 0 ↔
      MachineState.readWord input 32 = 0 ∧ guardDiff remainingChecks input = 0 := by
  rw [guardDiff_eq_zero_iff, guardDiff_eq_zero_iff]
  simp [WordsMatch, Data.checks, remainingChecks]
  tauto

def branchJumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1535
      stack := [UInt256.ofNat 1540, UInt256.ofNat 1] }

def fallbackJumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1539
      stack := [UInt256.ofNat 1553] }

def storeWord (mem : ByteArray) (addr w : Nat) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded w 32) addr

def answerMemory : ByteArray :=
  (storeWord ByteArray.empty 0 1)

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1549
      stack := []
      memory := answerMemory
      activeWords := UInt256.ofNat 1
      halt := .Returned
      hReturn := MachineState.readPadded answerMemory 31 1 }

theorem answerMemory_read :
    MachineState.readPadded answerMemory 31 1 = Precompile.natToBytes 1 1 := by
  decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.V2.State
