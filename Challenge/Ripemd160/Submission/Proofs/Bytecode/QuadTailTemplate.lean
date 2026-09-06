import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# Cached-factor consume tail template

The 419d031 helper leaves `[right.a,b,c,d,e, factor, left.b,c,d,e,a, ret] ++ rest`.
The consume tail permutes those live words onto the combine operands, writes the
five `evmCombine` stores, pops the leftover factor, and `JUMP`s. Eight following
`STOP` bytes are unreachable padding so later PCs and instruction indices stay.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailTemplate

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTail

def factor : UInt256 := UInt256.ofNat 0x100000001

def tailStartPC : UInt256 := UInt256.ofNat 0x9a9
def tailJumpPC : UInt256 := UInt256.ofNat 0x9fb

def swap5H : Instr := .op (.Swap ⟨4, by decide⟩)
def swap6H : Instr := .op (.Swap ⟨5, by decide⟩)
def swap7H : Instr := .op (.Swap ⟨6, by decide⟩)

def c0Instructions : List Instr :=
  [ swap3, swap1, swap7H,
    push1 (UInt256.ofNat 0x40), op .MLOAD, op .ADD, op .ADD,
    push4 mask, op .AND ]

def c1Instructions : List Instr :=
  [ swap3, swap1, swap7H,
    push1 (UInt256.ofNat 0x60), op .MLOAD, op .ADD, op .ADD,
    push4 mask, op .AND,
    push1 (UInt256.ofNat 0x40), op .MSTORE ]

def c2Instructions : List Instr :=
  [ swap1, swap6H,
    push1 (UInt256.ofNat 0x80), op .MLOAD, op .ADD, op .ADD,
    push4 mask, op .AND,
    push1 (UInt256.ofNat 0x60), op .MSTORE ]

def c3Instructions : List Instr :=
  [ swap5H, swap1, swap2,
    push1 (UInt256.ofNat 0xa0), op .MLOAD, op .ADD, op .ADD,
    push4 mask, op .AND,
    push1 (UInt256.ofNat 0x80), op .MSTORE ]

def c4Instructions : List Instr :=
  [ push1 (UInt256.ofNat 0x20), op .MLOAD, op .ADD, op .ADD,
    push4 mask, op .AND,
    push1 (UInt256.ofNat 0xa0), op .MSTORE ]

def storeH0Instructions : List Instr :=
  [ push1 (UInt256.ofNat 0x20), op .MSTORE ]

def cleanupInstructions : List Instr :=
  [ op .POP ]

def quadTailBeforeJumpTemplate : List Instr :=
  c0Instructions ++ c1Instructions ++ c2Instructions ++ c3Instructions ++
    c4Instructions ++ storeH0Instructions ++ cleanupInstructions

/-- Reachable consume body, including the return `JUMP`. -/
def consumeBody : List Instr :=
  quadTailBeforeJumpTemplate ++ [op .JUMP]

/-- Unreachable padding after the return `JUMP`. Not executed. -/
def paddingStops : List Instr :=
  [op .STOP, op .STOP, op .STOP, op .STOP,
   op .STOP, op .STOP, op .STOP, op .STOP, op .STOP]

/-- 62-instruction window: 53 reachable + 9 `STOP`. Preserves later PCs. -/
def quadTailWindow : List Instr :=
  consumeBody ++ paddingStops

/-- Executed template is the reachable body through `JUMP`. -/
def quadTailTemplate : List Instr :=
  consumeBody

def workingStack (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [ right.a, right.b, right.c, right.d, right.e,
    factor, left.b, left.c, left.d, left.e, left.a, ret ] ++ rest

def tailEntry (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := tailStartPC
    stack := workingStack left right ret rest }

def beforeJumpResult (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256) : State :=
  { StackTail.preJumpResult s left right ret rest with
    pc := tailJumpPC }

def finalResult (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256) : State :=
  { beforeJumpResult s left right ret rest with
    pc := ret
    stack := rest }

@[simp] theorem consumeBody_length : consumeBody.length = 53 := by
  rfl

@[simp] theorem paddingStops_length : paddingStops.length = 9 := by
  rfl

@[simp] theorem quadTailWindow_length : quadTailWindow.length = 62 := by
  rfl

@[simp] theorem quadTailTemplate_length : quadTailTemplate.length = 53 := by
  rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailTemplate
