import Challenge.Modexp.Benchmark.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Correct
import Challenge.Modexp.Submission.Proofs.Fast.Exp

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Benchmark

/-- Correctness of the submitted MODEXP bytecode.

Instruction 0 is `PUSH2 1314; JUMP`, so every execution enters the code appended
at byte 1314.  That code returns the result itself for an odd modulus wider than
32 bytes, and otherwise reaches the reference program body's `JUMPDEST` at
pc 1196 with an empty stack and untouched memory.  `Fast.Correct` joins the two
sides: `Fast.Setup` supplies the declining trace, `Fast.Exp` the returning one,
and the reference proof covers everything from pc 1196 on. -/
theorem candidate : Challenge.Modexp.Correct bytecode := by
  change Challenge.Modexp.Correct Challenge.Modexp.submissionBytecode
  exact Challenge.Modexp.Submission.Proofs.Fast.Correct.submission_correct_of
    Challenge.Modexp.Submission.Proofs.Fast.Exp.gasSteps_handled

end Challenge.Modexp.Benchmark
