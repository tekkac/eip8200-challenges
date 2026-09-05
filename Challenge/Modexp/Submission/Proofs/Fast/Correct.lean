import Challenge.Modexp.Submission.Proofs.Bytecode.SubmissionCorrect
import Challenge.Modexp.Submission.Proofs.Fast.Setup
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
/-!
# Top-level dispatch between the appended fast path and the reference body

Instruction 0 of the artifact is `PUSH2 1314; JUMP`, so every execution enters the
appended fast path.  The fast path either produces the result itself, or reaches the
reference program body's `JUMPDEST` at pc 1196 with an empty stack and untouched
memory, from which the pre-existing reference proof runs unchanged.

This module packages that case split.  The two sides are hypotheses, so the whole
integration is settled before the fast-path modules land: `Fast.Setup` supplies
`bail`, and `Fast.Exp` supplies `handled`.

`Challenge.EvmProof.GasSteps` carries a gas count, so it is a `Type`, not a `Prop`.
It therefore cannot sit under `∃ … ∧ …`; the success side states `Nonempty` of the
trace instead, and the trace is recovered with `Classical.choice`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Correct

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- The state the entry hop leaves: pc 1314, empty stack, memory untouched. -/
abbrev entryState (input : ByteArray) : State := Main.trampolineState input 1314

/-- The state the fast path leaves when it declines an input: pc 1196, empty
stack, memory untouched -- exactly the reference body's entry. -/
abbrev bodyState (input : ByteArray) : State := Main.trampolineState input 1196

/-- What the success side of the fast path must deliver for one input. -/
abbrev Handled (input : ByteArray) : Prop :=
  ∃ final : State,
    Nonempty (Challenge.EvmProof.GasSteps (entryState input) final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input)

/-- Everything the fast path must supply, as one record.

`Handles` is the fast path's own precondition; it is a `Prop` per input, and the two
traces cover its two sides.  `handled` is deliberately existential in the final state:
the fast path only has to reach *some* halted state whose result is `spec input`. -/
structure FastPath where
  Handles : ByteArray → Prop
  decide : ∀ input, Handles input ∨ ¬ Handles input
  bail : ∀ input, ValidInput input → ¬ Handles input →
    Challenge.EvmProof.GasSteps (entryState input) (bodyState input)
  handled : ∀ input, ValidInput input → Handles input → Handled input

/-- The halted state reached for one input, bundled with everything the challenge
statement needs about it.

Bundling is what makes the case split legal: the payload is a `Prop`, so the
`dite` lives in `Subtype` and never eliminates a `Prop` into a `Type`. -/
private theorem withGas_initialState (code cd : ByteArray) (gas : Nat) :
    Challenge.EvmProof.withGas (initialState code cd 0) gas = initialState code cd gas := rfl

open scoped Classical in
private noncomputable def chosenData (F : FastPath) (input : ByteArray) (hvalid : ValidInput input) :
    { final : State //
        Nonempty (Challenge.EvmProof.GasSteps
          (initialState submissionBytecode input 0) final) ∧
          final.isDone = true ∧ final.toResult = .returned (spec input) } :=
  if h : F.Handles input then
    ⟨Classical.choose (F.handled input hvalid h),
      ⟨⟨(Main.gasSteps_entryHop input).trans
          (Classical.choice (Classical.choose_spec (F.handled input hvalid h)).1)⟩,
        (Classical.choose_spec (F.handled input hvalid h)).2.1,
        (Classical.choose_spec (F.handled input hvalid h)).2.2⟩⟩
  else
    ⟨SubmissionCorrect.finalState input,
      ⟨⟨SubmissionCorrect.gasSteps_submission input hvalid
          ((Main.gasSteps_entryHop input).trans (F.bail input hvalid h))⟩,
        SubmissionCorrect.finalState_isDone input,
        SubmissionCorrect.finalState_result input hvalid⟩⟩

private noncomputable def chosenFinal (F : FastPath) (input : ByteArray)
    (hvalid : ValidInput input) : State :=
  (chosenData F input hvalid).1

private noncomputable def chosen_trace (F : FastPath) (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (chosenFinal F input hvalid) :=
  Classical.choice (chosenData F input hvalid).2.1

private theorem chosen_isDone (F : FastPath) (input : ByteArray) (hvalid : ValidInput input) :
    (chosenFinal F input hvalid).isDone = true :=
  (chosenData F input hvalid).2.2.1

private theorem chosen_result (F : FastPath) (input : ByteArray) (hvalid : ValidInput input) :
    (chosenFinal F input hvalid).toResult = .returned (spec input) :=
  (chosenData F input hvalid).2.2.2

theorem submissionDirectProof (F : FastPath) :
    Challenge.Modexp.ProofSupport.Bytecode.DirectProof submissionBytecode := by
  let Input := { calldata : ByteArray // ValidInput calldata }
  have h := Challenge.EvmProof.GasSteps.toEventuallyEvaluates
    (initial := fun input : Input => initialState submissionBytecode input.1 0)
    (final := fun input : Input => chosenFinal F input.1 input.2)
    (expected := fun input : Input => .returned (spec input.1))
    (fun input => chosen_trace F input.1 input.2)
    (fun input => chosen_isDone F input.1 input.2)
    (fun input => chosen_result F input.1 input.2)
  simpa [Challenge.Modexp.ProofSupport.Bytecode.DirectProof, Input,
    withGas_initialState] using h

theorem submission_correct (F : FastPath) : Correct submissionBytecode :=
  Challenge.Modexp.ProofSupport.Bytecode.correct_of_directProof
    (submissionDirectProof F)

/-- The concrete fast path.  Everything except the success-side trace is
discharged here from `Fast.Setup`, so the whole submission reduces to the single
obligation `handled`. -/
def fastPathOf
    (handled : ∀ input : ByteArray, ValidInput input →
        Challenge.Modexp.Submission.Proofs.Fast.Setup.FastPath input →
        Handled input) :
    FastPath where
  Handles := Challenge.Modexp.Submission.Proofs.Fast.Setup.FastPath
  decide := Challenge.Modexp.Submission.Proofs.Fast.Setup.fastPath_em
  bail := fun input _ h =>
    Challenge.Modexp.Submission.Proofs.Fast.Setup.gasSteps_fallback input h
  handled := handled

/-- The challenge statement, reduced to the success-side trace. -/
theorem submission_correct_of
    (handled : ∀ input : ByteArray, ValidInput input →
        Challenge.Modexp.Submission.Proofs.Fast.Setup.FastPath input →
        Handled input) :
    Correct submissionBytecode :=
  submission_correct (fastPathOf handled)

end Challenge.Modexp.Submission.Proofs.Fast.Correct
