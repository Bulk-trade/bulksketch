import BulksketchBridge.CanonicalizeWrapper
import BulksketchBridge.NativeCandidateDeflateDriver

namespace BulksketchBridge.ExecutionDriver

open Aeneas Aeneas.Std CanonicalizeRuntime CanonicalizeOrdering ExecutionDriverRuntime
open BulksketchBridge.DenseCoefficient RebuiltLfsr
open bulksketch.backend.contract bulksketch.decode.row bulksketch.decode.stages
open bulksketch.decode.scratch bulksketch.types
open bulksketch.decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution (run_next)

/-- The original generated canonicalizer with the checked value-level model
of the unsigned standard-library sort. -/
abbrev nativeCanonicalize : Canonicalize :=
  fun field kernels => bulksketch.decode.stages.Execution.canonicalize
    (fun (_ : core.cmp.Ord U64) => Aeneas.Std.DegreeProbeRuntime.sortUnsigned) field kernels

abbrev gf64Mask : U64 := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.MASK

abbrev canonicalStageCharge {K : Type} (self : Execution bulksketch.field.Gf64 K) (meter : WorkMeter) :=
  StageCharge.chargeResult meter (WorkSchedule.checkedCost (CanonicalizePrice.units self.budget.total))

abbrev selectedCanonicalRoots {K : Type} (self : Execution bulksketch.field.Gf64 K) (workspace : RowWorkspace) :=
  prefixSlice workspace.roots self.roots.count.val

def canonicalWritten {K : Type} (self : Execution bulksketch.field.Gf64 K)
    (workspace : RowWorkspace) : RowWorkspace :=
  { workspace with roots := DegreeProbeRuntime.canonicalize workspace.roots self.roots.count.val }

def canonicalStageResult {K : Type} (self : Execution bulksketch.field.Gf64 K)
    (workspace : RowWorkspace) (meter : WorkMeter) : RunFrame bulksketch.field.Gf64 K :=
  match canonicalStageCharge self meter with
  | (.Err error, finalMeter) => (.Err error, { self with state := .Error error }, workspace, id, finalMeter)
  | (.Ok (), finalMeter) =>
    if self.roots.count > self.budget.nonzero then
      (.Ok (progress .Canonicalization self), { self with state := .Failed .DegreeExceedsBudget },
        workspace, id, finalMeter)
    else
      let selected := selectedCanonicalRoots self workspace
      let ordered := Aeneas.Std.DegreeProbeRuntime.sortedWords selected
      (.Ok (progress .Canonicalization self),
        { self with state := if invalid gf64Mask ordered.val then .Failed .InvalidLocator else .Complete },
        canonicalWritten self workspace, id, finalMeter)

def ActualCanonicalStage : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (self : Execution bulksketch.field.Gf64 K) (input : RowInput) (workspace : RowWorkspace) (meter : WorkMeter),
    self.state = .Running .Canonicalization → self.degree_probe = none →
    (self.roots.count ≤ self.budget.nonzero → self.roots.count.val ≤ workspace.roots.length) →
    nativeCandidateDriver nativeCanonicalize kernels self input workspace meter =
      .ok (canonicalStageResult self workspace meter)

theorem canonical_stage_refines : ActualCanonicalStage := by
  intro K kernels self input workspace meter state probe room
  have exactMask : RootSetup.gf64Dictionary.MASK = .ok gf64Mask := rfl
  have lower := CanonicalizeWrapper.canonicalize_refines _
    CanonicalizeWrapper.unsigned_sort_law RootSetup.gf64Dictionary kernels gf64Mask
    self workspace meter exactMask room
  change nativeCanonicalize RootSetup.gf64Dictionary kernels self workspace meter =
    CanonicalizeWrapper.expected gf64Mask self workspace meter at lower
  change run_next RootRun.nativeCalls RootRun.nativeDivRem nativeCanonicalize
    RootSetup.gf64Dictionary kernels self input workspace meter = _
  rw [run_next_refines RootRun.nativeCalls RootRun.nativeDivRem nativeCanonicalize
    RootSetup.gf64Dictionary kernels self input workspace meter, expectedRunNext, state]
  dsimp only
  rw [execute_refines RootRun.nativeCalls RootRun.nativeDivRem nativeCanonicalize
    RootSetup.gf64Dictionary kernels self .Canonicalization input workspace meter, expectedExecute, probe]
  rw [lower]
  unfold CanonicalizeWrapper.expected canonicalStageResult
  change _ = Result.ok _
  cases cost : canonicalStageCharge self meter with
  | mk outcome finalMeter =>
    cases outcome with
    | Err error => simp only [cost, bind_ok, transition]
    | Ok result =>
      cases result
      by_cases excess : self.roots.count > self.budget.nonzero
      · simp only [cost, excess, ite_true, bind_ok, transition]
      · simp only [cost, excess, ite_false, bind_ok, CanonicalizeOrdering.order_words_eq_sorted]
        let ordered := Aeneas.Std.DegreeProbeRuntime.sortedWords (selectedCanonicalRoots self workspace)
        by_cases bad : invalid gf64Mask ordered.val = true
        · simp [bad, ordered, transition, canonicalWritten, DegreeProbeRuntime.canonicalize]
        · simp [bad, ordered, transition, canonicalWritten, DegreeProbeRuntime.canonicalize]

theorem canonical_stage_written {K : Type} (self : Execution bulksketch.field.Gf64 K)
    (workspace : RowWorkspace) (room : self.roots.count.val ≤ workspace.roots.length) :
    (canonicalWritten self workspace).roots.length = workspace.roots.length ∧
    (canonicalWritten self workspace).roots.val.take self.roots.count.val =
      (Aeneas.Std.DegreeProbeRuntime.sortedWords (selectedCanonicalRoots self workspace)).val ∧
    (canonicalWritten self workspace).roots.val.drop self.roots.count.val =
      workspace.roots.val.drop self.roots.count.val :=
  DegreeProbeRuntime.canonicalize_frame workspace.roots self.roots.count.val room

theorem gf64_valid_word (word : U64) : validWord gf64Mask word ↔ word.bv ≠ 0 := by
  have inverse : ~~~gf64Mask.bv = (0 : BitVec 64) := by
    unfold gf64Mask bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.MASK
    decide
  simp [validWord, inverse]

theorem canonical_stage_paid_iff {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (self : Execution bulksketch.field.Gf64 K) (input : RowInput) (workspace : RowWorkspace)
    (meter finalMeter : WorkMeter) (state : self.state = .Running .Canonicalization)
    (probe : self.degree_probe = none)
    (paid : canonicalStageCharge self meter = (.Ok (), finalMeter))
    (admitted : self.roots.count ≤ self.budget.nonzero)
    (room : self.roots.count.val ≤ workspace.roots.length) :
    nativeCandidateDriver nativeCanonicalize kernels self input workspace meter =
      .ok (.Ok (progress .Canonicalization self), { self with state := .Complete },
        canonicalWritten self workspace, id, finalMeter) ↔
      (∀ word ∈ (selectedCanonicalRoots self workspace).val, word.bv ≠ 0) ∧
      (selectedCanonicalRoots self workspace).val.Nodup := by
  rw [canonical_stage_refines kernels self input workspace meter state probe (fun _ => room),
    canonicalStageResult, paid]
  have within : ¬ self.roots.count > self.budget.nonzero := by
    change ¬ self.budget.nonzero.val < self.roots.count.val
    change self.roots.count.val ≤ self.budget.nonzero.val at admitted
    omega
  dsimp only
  rw [ite_eq_right within]
  simp only [← gf64_valid_word]
  rw [← complete_word_validation, order_words_eq_sorted]
  cases invalid gf64Mask (Aeneas.Std.DegreeProbeRuntime.sortedWords
    (selectedCanonicalRoots self workspace)).val <;> simp

/-- A failed canonicalization charge never accesses the selected root prefix. -/
theorem canonical_stage_charge_error {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (self : Execution bulksketch.field.Gf64 K) (input : RowInput) (workspace : RowWorkspace)
    (meter finalMeter : WorkMeter) (error : DecodeError)
    (state : self.state = .Running .Canonicalization) (probe : self.degree_probe = none)
    (charged : canonicalStageCharge self meter = (.Err error, finalMeter)) :
    nativeCandidateDriver nativeCanonicalize kernels self input workspace meter =
      .ok (.Err error, { self with state := .Error error }, workspace, id, finalMeter) := by
  apply run_next_return RootRun.nativeCalls RootRun.nativeDivRem nativeCanonicalize RootSetup.gf64Dictionary
    kernels self .Canonicalization input workspace meter (.Err error, self, workspace, id, finalMeter) state
  rw [execute_refines RootRun.nativeCalls RootRun.nativeDivRem nativeCanonicalize RootSetup.gf64Dictionary
    kernels self .Canonicalization input workspace meter, expectedExecute, probe]
  change bulksketch.decode.stages.Execution.canonicalize _ RootSetup.gf64Dictionary kernels self workspace meter = _
  unfold bulksketch.decode.stages.Execution.canonicalize
  unfold canonicalStageCharge at charged
  rw [CanonicalizePrice.exact_charge RootSetup.gf64Dictionary kernels meter self.budget.total, charged, bind_ok]
  simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  rfl

#print axioms canonical_stage_refines
#print axioms canonical_stage_written
#print axioms canonical_stage_paid_iff
#print axioms canonical_stage_charge_error

end BulksketchBridge.ExecutionDriver
