import BulksketchBridge.PublicationWriteAdmission
import BulksketchBridge.NativeCanonicalCompleted
import BulksketchBridge.PublicationWriteDecoded

namespace BulksketchBridge.PublicationWrite

open Aeneas.Std Algebra.Gf64 Polynomial
open ExecutionDriver RebuiltLfsr DenseCoefficient
open bulksketch.backend.contract bulksketch.decode.row bulksketch.decode.stages
open bulksketch.decode.scratch bulksketch.types bulksketch.sketch.api

set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

/-- Exact local admission for an already verified canonicalization stage.
The row budget relation records the original request's zero reservation. -/
structure CanonicalAdmission {K : Type} {self : Execution bulksketch.field.Gf64 K}
    {workspace : RowWorkspace} {meter finalMeter : WorkMeter}
    {locator : Polynomial Field} {zero : Bool} : Prop where
  state : self.state = .Running .Canonicalization
  noProbe : self.degree_probe = none
  paid : canonicalStageCharge self meter = (.Ok (), finalMeter)
  rootBudget : self.roots.count ≤ self.budget.nonzero
  rootRoom : self.roots.count.val ≤ workspace.roots.length
  represented : RootRun.emittedProduct self.roots workspace = locator
  distinct : locator.roots.Nodup
  nonzero : ∀ point, locator.IsRoot point → point ≠ 0
  zeroReserve : self.budget.total.val = self.budget.nonzero.val + zeroWidth zero

/-- The original row driver and completed-result accessor supply either the
native Equal outcome or precisely the writer's valid decoded slice. -/
def ActualCanonicalPublicationAdmission : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (self : Execution bulksketch.field.Gf64 K) (input : RowInput) (workspace : RowWorkspace)
    (meter finalMeter : WorkMeter) (locator : Polynomial Field) (zero : Bool),
    CanonicalAdmission (self := self) (workspace := workspace) (meter := meter)
      (finalMeter := finalMeter) (locator := locator) (zero := zero) →
    let after := { self with state := .Complete }
    let written := canonicalWritten self workspace
    let words := prefixSlice written.roots self.roots.count.val
    nativeCandidateDriver nativeCanonicalize kernels self input workspace meter =
      .ok (.Ok (progress .Canonicalization self), after, written, id, finalMeter) ∧
    (∀ point, locator.IsRoot point ↔ ∃ word ∈ words.val, point = toField word.bv) ∧
    if self.roots.count = 0#usize ∧ self.budget.total = self.budget.nonzero then
      Execution.completed_result RootSetup.gf64Dictionary kernels after written = .ok (.Ok .Equal) ∧
        locator = 1 ∧ zero = false
    else
      Execution.completed_result RootSetup.gf64Dictionary kernels after written = .ok (.Ok (.Decoded words)) ∧
        words.length = self.roots.count.val ∧ validDecoded words zero ∧
        zeroWidth zero + words.length ≤ self.budget.total.val

theorem canonical_publication_admission : ActualCanonicalPublicationAdmission := by
  intro K kernels self input workspace meter finalMeter locator zero admitted after written words
  obtain ⟨state, noProbe, paid, rootBudget, rootRoom, represented, simple, nonzero, zeroReserve⟩ := admitted
  obtain ⟨ran, ascending, distinct, roots, outcome⟩ :=
    native_canonical_completed_locator kernels self input workspace meter finalMeter locator
      state noProbe paid rootBudget rootRoom
      represented simple nonzero
  refine ⟨ran, roots, ?_⟩
  by_cases equal : self.roots.count = 0#usize ∧ self.budget.total = self.budget.nonzero
  · rw [ite_eq_left equal] at outcome ⊢
    have zeroAbsent : zero = false := by
      cases zero with
      | false => rfl
      | true =>
        have reserve := zeroReserve
        rw [equal.2, zeroWidth] at reserve
        simp at reserve
    exact ⟨outcome.1, outcome.2, zeroAbsent⟩
  · rw [ite_eq_right equal] at outcome ⊢
    obtain ⟨completed, width⟩ := outcome
    have nonempty : words.val ≠ [] ∨ zero = true := by
      by_cases empty : words.val = []
      · right
        cases zero with
        | true => rfl
        | false =>
          exfalso
          apply equal
          have none : words.length = 0 := by simp [Slice.length, empty]
          have count : self.roots.count = 0#usize := UScalar.eq_of_val_eq (width.symm.trans none)
          have reserve := zeroReserve
          simp only [zeroWidth, Bool.false_eq_true, ite_false, Nat.add_zero] at reserve
          exact ⟨count, UScalar.eq_of_val_eq reserve⟩
      · exact Or.inl empty
    have noZero (word : U64) (member : word ∈ words.val) : word ≠ 0#u64 := by
      intro zeroWord
      have isRoot : locator.IsRoot (toField word.bv) :=
        (roots (toField word.bv)).mpr ⟨word, member, rfl⟩
      apply nonzero _ isRoot
      rw [zeroWord]
      exact toField_zero
    have quota : zeroWidth zero + words.length ≤ self.budget.total.val := by
      have exact := zeroReserve
      have room : self.roots.count.val ≤ self.budget.nonzero.val := rootBudget
      change words.length = self.roots.count.val at width
      omega
    exact ⟨completed, width, valid_decoded_of_canonical words zero nonempty ascending distinct noZero, quota⟩

#print axioms canonical_publication_admission

end BulksketchBridge.PublicationWrite
