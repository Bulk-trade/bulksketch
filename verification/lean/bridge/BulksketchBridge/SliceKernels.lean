import BulksketchBridge.SliceKernelChallenges
import BulksketchBridge.Algebra.WordNative

namespace BulksketchBridge.SliceKernels

open Aeneas Aeneas.Std Aeneas.Std.WP
open bulksketch.backend.contract
open BulksketchBridge.Algebra.Gf64 SliceKernelChallenges

private theorem normal_of_spec {α : Type} (computation : Result α) (post : α → Prop)
    (proof : computation ⦃ post ⦄) :
    ∃ value, computation = Result.ok value ∧ post value := by
  cases computation using Result.cases with
  | ret value => exact ⟨value, rfl, (spec_ok value).mp proof⟩
  | vis effect continuation => exact False.elim ((spec_vis effect continuation).mp proof)
  | div => exact False.elim ((spec_div).mp proof)

private def reverseAt (endpoint : Usize) :
    core.iter.adapters.rev.Rev (core.ops.range.Range Usize) :=
  ⟨{ start := 1#usize, «end» := endpoint }⟩

private theorem reverse_step (endpoint : Usize) (active : 1 < endpoint.val) :
    ∃ index : Usize, index.val = endpoint.val - 1 ∧
      core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
        (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
        (reverseAt endpoint) = Result.ok (some index, reverseAt index) := by
  let index : Usize := UScalar.ofNatCore (endpoint.val - 1) (by
    have bounded := endpoint.hBounds
    omega)
  refine ⟨index, by simp [index], ?_⟩
  have predecessorFits : 1 ≤ endpoint.val := by omega
  simp [reverseAt, core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.backward_checked, core.cmp.PartialOrdUsize,
    core.cmp.impls.PartialOrdUsize.lt, liftFun2,
    active, predecessorFits, index]

private theorem reverse_done (endpoint : Usize) (inactive : ¬ 1 < endpoint.val) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
      (reverseAt endpoint) = Result.ok (none, reverseAt endpoint) := by
  simp [reverseAt, core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep, core.cmp.PartialOrdUsize,
    core.cmp.impls.PartialOrdUsize.lt, liftFun2, inactive]

private theorem read_normal (words : Slice U64) (index : Usize)
    (bounded : index.val < words.length) :
    Slice.index_usize words index = Result.ok words[index.val]! := by
  obtain ⟨value, normal, exactWord⟩ := normal_of_spec _ _
    (Slice.index_usize_spec words index bounded)
  rw [normal, exactWord, Slice.getElem!_Nat_eq]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! words.val index.val bounded)

/-- Every step consumes one descending index, leaving all earlier words intact.
The suffix already has its exact product coefficients. -/
private theorem loop_refines {Backend : Type}
    (kernels : BulkKernels Backend bulksketch.field.Gf64)
    (nativeMul : ∀ left right, kernels.ArithmeticInst.mul left right =
      bulksketch.field.gf64.mul bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField left right)
    (original : Slice U64) (root : U64) (endpoint : Usize) (current : Slice U64)
    (bounded : endpoint.val ≤ original.length) (lengthEq : current.length = original.length)
    (words : ∀ j : Nat, j < original.length → current[j]! =
      if j < endpoint.val then original[j]! else coefficientAfter original root j) :
    ∃ output : Slice U64,
      BulkKernels.multiply_linear.default_loop kernels (reverseAt endpoint) current root = Result.ok output ∧
      output.length = original.length ∧
      ∀ j : Nat, j < original.length → output[j]! = coefficientAfter original root j := by
  suffices ∀ remaining (endpoint : Usize) (current : Slice U64),
      endpoint.val = remaining → endpoint.val ≤ original.length →
      current.length = original.length →
      (∀ j : Nat, j < original.length → current[j]! =
        if j < endpoint.val then original[j]! else coefficientAfter original root j) →
      ∃ output : Slice U64,
        BulkKernels.multiply_linear.default_loop kernels (reverseAt endpoint) current root = Result.ok output ∧
        output.length = original.length ∧
        ∀ j : Nat, j < original.length → output[j]! = coefficientAfter original root j from
    this endpoint.val endpoint current rfl bounded lengthEq words
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining inductionHypothesis =>
    intro endpoint current remainingEq bounded lengthEq words
    by_cases active : 1 < endpoint.val
    · obtain ⟨index, indexVal, nextNormal⟩ := reverse_step endpoint active
      have indexBound : index.val < original.length := by omega
      have previousExists : (1#usize).val ≤ index.val := by simp; omega
      obtain ⟨previous, subNormal, previousPost⟩ := normal_of_spec _ _
        (Usize.sub_spec (x := index) (y := 1#usize) previousExists)
      have previousVal : previous.val = index.val - 1 := by simpa using previousPost.1
      have indexRead := read_normal current index (by omega)
      have previousRead := read_normal current previous (by omega)
      have indexOld : current[index.val]! = original[index.val]! := by
        simpa only [ite_eq_left (show index.val < endpoint.val by omega)] using words index.val indexBound
      have previousOld : current[previous.val]! = original[previous.val]! := by
        simpa only [ite_eq_left (show previous.val < endpoint.val by omega)] using
          words previous.val (by omega)
      obtain ⟨updated, updateNormal, updatedEq⟩ := normal_of_spec _ _
        (Slice.update_spec current index (coefficientAfter original root index.val) (by omega))
      have bodyNormal : BulkKernels.multiply_linear.default_loop.body
          kernels root (reverseAt endpoint) current =
          Result.ok (ControlFlow.cont (reverseAt index, updated)) := by
        simp only [BulkKernels.multiply_linear.default_loop.body, nextNormal, bind_ok]
        dsimp! only
        simp only [subNormal, bind_ok, previousRead, previousOld, nativeMul, native_mul_word,
          indexRead, indexOld, lift]
        rw [previousVal]
        have changed : index.val ≠ 0 := by omega
        simp only [coefficientAfter, ite_eq_right changed] at updateNormal
        simp only [updateNormal, bind_ok]
      have updatedLength : updated.length = original.length := by
        rw [updatedEq, Slice.set_length, lengthEq]
      have updatedWords : ∀ j : Nat, j < original.length → updated[j]! =
          if j < index.val then original[j]! else coefficientAfter original root j := by
        intro j bound
        rw [updatedEq]
        by_cases equal : index.val = j
        · rw [Slice.getElem!_Nat_set_eq current index j _ ⟨equal, by omega⟩,
            ite_eq_right (show ¬ j < index.val by omega), equal]
        · rw [Slice.getElem!_Nat_set_ne current index j _ equal, words j bound]
          by_cases untouched : j < index.val
          · rw [ite_eq_left untouched, ite_eq_left (show j < endpoint.val by omega)]
          · rw [ite_eq_right untouched, ite_eq_right (show ¬ j < endpoint.val by omega)]
      obtain ⟨output, normal, outputLength, outputWords⟩ := inductionHypothesis
        index.val (by omega) index updated rfl (by omega) updatedLength updatedWords
      refine ⟨output, ?_, outputLength, outputWords⟩
      unfold BulkKernels.multiply_linear.default_loop
      unfold loop
      dsimp only
      rw [bodyNormal]
      simp only [bind_ok]
      exact normal
    · refine ⟨current, ?_, lengthEq, ?_⟩
      · unfold BulkKernels.multiply_linear.default_loop
        unfold loop
        dsimp only
        simp only [BulkKernels.multiply_linear.default_loop.body, reverse_done endpoint active, bind_ok]
        dsimp! only
        simp only [bind_ok]
      · intro j bound
        rw [words j bound]
        by_cases untouched : j < endpoint.val
        · have zero : j = 0 := by omega
          subst j
          simp [untouched, coefficientAfter]
        · rw [ite_eq_right untouched]

/-- The actual default preserves the complete slice length and computes every
coefficient of the fixed-length product, including empty and singleton slices. -/
theorem multiply_linear_refines : actualMultiplyLinearReturnsExactFrame := by
  intro Backend kernels nativeMul coefficients root
  unfold BulkKernels.multiply_linear.default
  simp only [core.iter.traits.iterator.Iterator.rev.trait_default,
    core.iter.traits.iterator.Iterator.rev.default, bind_ok]
  change ∃ output : Slice U64,
    BulkKernels.multiply_linear.default_loop kernels (reverseAt coefficients.len)
      coefficients root = Result.ok output ∧
    output.length = coefficients.length ∧
    ∀ j : Nat, j < coefficients.length → output[j]! = coefficientAfter coefficients root j
  exact loop_refines kernels nativeMul coefficients root coefficients.len coefficients
    (by rw [Slice.len_val]) rfl (by intro j bound; simp [bound])

theorem square_mod_fallback_refines : actualSquareModFallbackPreservesBuffers := by
  intro Backend Field a table dst raw
  rfl

end BulksketchBridge.SliceKernels
