import BulksketchBridge.NativeCompletedResult
import BulksketchBridge.RootEmissionProduct

namespace BulksketchBridge.CompletedResult

open Aeneas.Std Algebra.Gf64 Polynomial DenseCoefficient RebuiltLfsr
open RootRun
open bulksketch.backend.contract bulksketch.decode.row bulksketch.decode.stages bulksketch.decode.scratch

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

theorem roots_product_root (words : List U64) (point : Field) :
    (rootsProduct words).IsRoot point ↔ ∃ word ∈ words, point = toField word.bv := by
  induction words with
  | nil => simp [rootsProduct, Polynomial.IsRoot.def]
  | cons first rest ih =>
    change ((X + C (toField first.bv)) * rootsProduct rest).eval point = 0 ↔ _
    rw [eval_mul, mul_eq_zero, eval_add, eval_X, eval_C]
    have firstRoot : point + toField first.bv = 0 ↔ point = toField first.bv := by
      simpa only [sub_eq_add_neg, CharTwo.neg_eq] using (sub_eq_zero : point - toField first.bv = 0 ↔ _)
    rw [firstRoot, show (rootsProduct rest).eval point = 0 ↔ _ from ih]
    constructor
    · rintro (equal | ⟨word, inRest, exactPoint⟩)
      · exact ⟨first, List.mem_cons_self, equal⟩
      · exact ⟨word, List.mem_cons_of_mem first inRest, exactPoint⟩
    · rintro ⟨word, present, exactPoint⟩
      rcases List.mem_cons.mp present with rfl | inRest
      · exact Or.inl exactPoint
      · exact Or.inr ⟨word, inRest, exactPoint⟩

/-- Once the driver is complete and its emitted prefix represents the
locator, the actual borrowed row result has exactly the locator roots.
The separate Equal result corresponds to the empty nonzero product. -/
def ActualNativeCompletedLocator : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (self : Execution bulksketch.field.Gf64 K) (workspace : RowWorkspace) (locator : Polynomial Field),
    self.state = .Complete → self.roots.count.val ≤ workspace.roots.length →
    emittedProduct self.roots workspace = locator →
    let words := prefixSlice workspace.roots self.roots.count.val
    (∀ point, locator.IsRoot point ↔ ∃ word ∈ words.val, point = toField word.bv) ∧
    if self.roots.count = 0#usize ∧ self.budget.total = self.budget.nonzero then
      Execution.completed_result RootSetup.gf64Dictionary kernels self workspace = .ok (.Ok .Equal) ∧
      locator = 1
    else
      Execution.completed_result RootSetup.gf64Dictionary kernels self workspace = .ok (.Ok (.Decoded words)) ∧
      words.length = self.roots.count.val

theorem native_completed_locator : ActualNativeCompletedLocator := by
  intro K kernels self workspace locator state room represented words
  have exactRoot (point : Field) : locator.IsRoot point ↔ ∃ word ∈ words.val, point = toField word.bv := by
    rw [← represented]
    simpa only [emittedProduct, words, prefixSlice, Slice.from_val] using
      roots_product_root words.val point
  refine ⟨exactRoot, ?_⟩
  have native := native_completed_result RootSetup.gf64Dictionary kernels self workspace
  rw [outcome, state] at native
  dsimp! only at native
  by_cases empty : self.roots.count = 0#usize ∧ self.budget.total = self.budget.nonzero
  · rw [ite_eq_left empty]
    rw [ite_eq_left empty] at native
    refine ⟨native, ?_⟩
    rw [← represented]
    simp only [emittedProduct, empty.1, show (0#usize).val = 0 from rfl, List.take_zero,
      rootsProduct, List.map_nil, List.prod_nil]
  · rw [ite_eq_right empty]
    rw [ite_eq_right empty, decoded, ite_eq_left room] at native
    exact ⟨native, (prefix_length _ _).trans (Nat.min_eq_left room)⟩

#print axioms native_completed_locator

end BulksketchBridge.CompletedResult
