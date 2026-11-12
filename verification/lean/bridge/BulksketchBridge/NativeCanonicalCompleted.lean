import BulksketchBridge.NativeCanonicalizeDriver
import BulksketchBridge.CompletedLocator
import BulksketchBridge.RootEmittedValidity

namespace BulksketchBridge.ExecutionDriver

open Aeneas.Std Algebra.Gf64 Polynomial DenseCoefficient RebuiltLfsr
open bulksketch.backend.contract bulksketch.decode.row bulksketch.decode.stages
open bulksketch.decode.scratch bulksketch.types

theorem canonical_preserves_emitted_product {K : Type} (self : Execution bulksketch.field.Gf64 K)
    (workspace : RowWorkspace) (room : self.roots.count.val ≤ workspace.roots.length) :
    RootRun.emittedProduct self.roots (canonicalWritten self workspace) =
      RootRun.emittedProduct self.roots workspace := by
  have exact := (canonical_stage_written self workspace room).2.1
  unfold RootRun.emittedProduct
  rw [exact]
  unfold RootRun.rootsProduct
  apply List.Perm.prod_eq
  simpa only [selectedCanonicalRoots, prefixSlice, Slice.from_val] using
    (DegreeProbeRuntime.sortedWords_perm (selectedCanonicalRoots self workspace)).map
      (fun word : U64 => X + C (toField word.bv))

/-- An admitted paid canonicalization followed by the native completed-result
borrow returns the sorted prefix of exactly the represented locator roots. -/
def ActualCanonicalCompletedLocator : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (self : Execution bulksketch.field.Gf64 K) (input : RowInput) (workspace : RowWorkspace)
    (meter finalMeter : WorkMeter) (locator : Polynomial Field),
    self.state = .Running .Canonicalization → self.degree_probe = none →
    canonicalStageCharge self meter = (.Ok (), finalMeter) →
    self.roots.count ≤ self.budget.nonzero → self.roots.count.val ≤ workspace.roots.length →
    RootRun.emittedProduct self.roots workspace = locator →
    locator.roots.Nodup → (∀ point, locator.IsRoot point → point ≠ 0) →
    let after := { self with state := .Complete }
    let written := canonicalWritten self workspace
    let words := prefixSlice written.roots self.roots.count.val
    nativeCandidateDriver nativeCanonicalize kernels self input workspace meter =
      .ok (.Ok (progress .Canonicalization self), after, written, id, finalMeter) ∧
    words.val.Pairwise Aeneas.Std.DegreeProbeRuntime.ordered ∧ words.val.Nodup ∧
    (∀ point, locator.IsRoot point ↔ ∃ word ∈ words.val, point = toField word.bv) ∧
    if self.roots.count = 0#usize ∧ self.budget.total = self.budget.nonzero then
      Execution.completed_result RootSetup.gf64Dictionary kernels after written = .ok (.Ok .Equal) ∧ locator = 1
    else
      Execution.completed_result RootSetup.gf64Dictionary kernels after written = .ok (.Ok (.Decoded words)) ∧
        words.length = self.roots.count.val

theorem native_canonical_completed_locator : ActualCanonicalCompletedLocator := by
  intro K kernels self input workspace meter finalMeter locator state probe paid admitted room represented simple noZero
  have valid := RootRun.emitted_words_valid (selectedCanonicalRoots self workspace).val locator
    (by simpa only [RootRun.emittedProduct, selectedCanonicalRoots, prefixSlice, Slice.from_val] using represented)
    simple noZero
  obtain ⟨nonzero, distinct⟩ := valid
  let after := { self with state := .Complete }
  let written := canonicalWritten self workspace
  let words := prefixSlice written.roots self.roots.count.val
  have frame := canonical_stage_written self workspace room
  have afterRoom : after.roots.count.val ≤ written.roots.length := frame.1.symm ▸ room
  have sameProduct : RootRun.emittedProduct after.roots written = locator :=
    (canonical_preserves_emitted_product self workspace room).trans represented
  have closed := CompletedResult.native_completed_locator kernels after written locator rfl afterRoom sameProduct
  have order : words.val = (Aeneas.Std.DegreeProbeRuntime.sortedWords
    (selectedCanonicalRoots self workspace)).val := by
    simpa only [words, written, prefixSlice, Slice.from_val] using frame.2.1
  refine ⟨(canonical_stage_paid_iff kernels self input workspace meter finalMeter
    state probe paid admitted room).mpr ⟨nonzero, distinct⟩, ?_, ?_, closed⟩
  · rw [order]
    exact DegreeProbeRuntime.sortedWords_ordered _
  · rw [order]
    exact (DegreeProbeRuntime.sortedWords_perm _).nodup_iff.mpr distinct

#print axioms native_canonical_completed_locator

end BulksketchBridge.ExecutionDriver
