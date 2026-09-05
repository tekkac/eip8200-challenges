import Challenge.EvmProof.Bytecode
import Challenge.Modexp.Submission.Bytes
import EvmSemantics.Data.Hex
set_option warningAsError true
set_option maxRecDepth 10000

namespace Challenge.Modexp

/-- Canonical hexadecimal form of the frozen artifact. -/
def submissionHex : String := (include_str "bytecode.hex").trimAscii.copy

/-- Frozen verified-compiler output targeted by the direct EVM proof. -/
def submissionBytecode : ByteArray := submissionBytes

@[simp] theorem submissionBytecode_size : submissionBytecode.size = 3000 := by
  change submissionBytes.size = 3000
  exact submissionBytes_size

/-- Generic disassembly round-trip for the exact submitted bytes. -/
theorem submissionBytecode_roundtrip :
    Challenge.EvmProof.Bytecode.assemble
      (Challenge.EvmProof.Bytecode.disassemble submissionBytecode) = submissionBytecode :=
  Challenge.EvmProof.Bytecode.assemble_disassemble _

end Challenge.Modexp
