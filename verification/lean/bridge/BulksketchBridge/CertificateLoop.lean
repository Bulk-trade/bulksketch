import Arithmetic.CertificateGenerated
import BulksketchBridge.RebuiltLocatorLoop
import BulksketchBridge.InverseFieldSpec
import BulksketchBridge.Algebra.WordNative

namespace BulksketchBridge.Certificate

open Aeneas Aeneas.Std Aeneas.Std.WP Algebra.Gf64 RebuiltLfsr
open bulksketch.backend.contract bulksketch.decode.deg34

abbrev fieldDictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
abbrev mulWord := Inverse.multiplyNativeWord
abbrev NativeMul {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) :=
  ∀ left right, kernels.ArithmeticInst.mul left right = bulksketch.field.gf64.mul fieldDictionary left right

/-- The original descending loop only writes positive indices. -/
def descend (root : U64) : Nat → Slice U64 → Slice U64
  | 0, words => words
  | j + 1, words =>
    descend root j (words.setAtNat (j + 1) (words[j]! ^^^ mulWord root words[j + 1]!))

/-- A single outer step writes the new leading coefficient, descends, then updates the constant. -/
def productStep (words : Slice U64) (root : U64) (degree : Nat) : Slice U64 :=
  let shifted := descend root degree (words.setAtNat (degree + 1) words[degree]!)
  shifted.setAtNat 0 (mulWord root shifted[0]!)

def productFrom (roots : Slice U64) (words : Slice U64) (degree : Nat) : Nat → Slice U64
  | 0 => words
  | count + 1 => productFrom roots (productStep words roots[degree]! degree) (degree + 1) count

@[simp] theorem descend_length (root : U64) (degree : Nat) (words : Slice U64) :
    (descend root degree words).length = words.length := by
  induction degree generalizing words with
  | zero => rfl
  | succ degree ih => simp [descend, ih, Slice.setAtNat_length]

@[simp] theorem productStep_length (words : Slice U64) (root : U64) (degree : Nat) :
    (productStep words root degree).length = words.length := by
  simp [productStep, Slice.setAtNat_length]

private abbrev RevInclusive := core.iter.adapters.rev.Rev (core.ops.range.RangeInclusive Usize)

private def reverseAt (endpoint : Usize) (exhausted : Bool) : RevInclusive :=
  ⟨⟨1#usize, endpoint, exhausted⟩⟩

private abbrev nextRev := core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
  (bulksketch.core.ops.range.RangeInclusive.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
    core.iter.range.StepUsize)

private theorem reverse_done (endpoint : Usize) (exhausted : Bool)
    (stop : (if exhausted then 0 else endpoint.val) = 0) :
    nextRev (reverseAt endpoint exhausted) = Result.ok (none, reverseAt endpoint exhausted) := by
  cases exhausted with
  | true =>
    simp [nextRev, reverseAt, core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
      core.ops.range.RangeInclusive.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
      core.ops.range.RangeInclusive.is_empty]
  | false =>
    have zero : endpoint.val = 0 := stop
    have notLe : ¬ 1 ≤ endpoint.val := by omega
    simp [nextRev, reverseAt, core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
      core.ops.range.RangeInclusive.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
      core.ops.range.RangeInclusive.is_empty, core.iter.range.StepUsize,
      core.iter.range.UScalarStep, core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.le,
      liftFun2, notLe, pure]

private theorem reverse_step (endpoint : Usize) (positive : 0 < endpoint.val) :
    ∃ previous : Usize, ∃ exhausted : Bool,
      nextRev (reverseAt endpoint false) = Result.ok (some endpoint, reverseAt previous exhausted) ∧
      (if exhausted then 0 else previous.val) = endpoint.val - 1 := by
  have leOne : 1 ≤ endpoint.val := by omega
  by_cases one : endpoint.val = 1
  · refine ⟨endpoint, true, ?_, by simp [one]⟩
    simp [nextRev, reverseAt, core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
      core.ops.range.RangeInclusive.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
      core.ops.range.RangeInclusive.is_empty, core.iter.range.StepUsize,
      core.iter.range.UScalarStep, core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.le,
      core.cmp.impls.PartialOrdUsize.lt, core.clone.CloneUsize, liftFun2, liftFun1, one, pure]
  · have greater : 1 < endpoint.val := by omega
    let previous : Usize := UScalar.ofNatCore (endpoint.val - 1) (by
      have bounded := endpoint.hBounds
      omega)
    refine ⟨previous, false, ?_, by simp [previous]⟩
    simp [nextRev, reverseAt, core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
      core.ops.range.RangeInclusive.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
      core.ops.range.RangeInclusive.is_empty, core.iter.range.StepUsize,
      core.iter.range.UScalarStep, core.iter.range.UScalarStep.backward_checked,
      core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.le, core.cmp.impls.PartialOrdUsize.lt,
      liftFun2, leOne, greater, previous, pure]

private theorem read_normal (words : Slice U64) (index : Usize)
    (bounded : index.val < words.length) : Slice.index_usize words index = Result.ok words[index.val]! := by
  obtain ⟨value, normal, exactWord⟩ := RawMulTable.normal_of_spec _ _ (Slice.index_usize_spec words index bounded)
  rw [normal, exactWord, Slice.getElem!_Nat_eq]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! words.val index.val bounded)

private theorem update_normal (words : Slice U64) (index : Usize) (value : U64)
    (bounded : index.val < words.length) :
    Slice.update words index value = Result.ok (words.setAtNat index.val value) := by
  obtain ⟨output, normal, exactOutput⟩ := RawMulTable.normal_of_spec _ _ (Slice.update_spec words index value bounded)
  rw [normal, exactOutput]
  rfl

private theorem inner_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (mul : NativeMul kernels) (root : U64) (words : Slice U64)
    (endpoint : Usize) (exhausted : Bool) (remaining : Nat)
    (count : (if exhausted then 0 else endpoint.val) = remaining) (bound : remaining < words.length) :
    certificate_loop0_loop0 fieldDictionary kernels (reverseAt endpoint exhausted) words root =
      Result.ok (descend root remaining words) := by
  induction remaining generalizing endpoint exhausted words with
  | zero =>
    unfold certificate_loop0_loop0 loop
    dsimp only
    simp only [certificate_loop0_loop0.body, reverse_done endpoint exhausted count, bind_ok]
    dsimp! only
    simp only [bind_ok]
  | succ remaining ih =>
    have openRange : exhausted = false := by cases exhausted <;> simp_all
    subst exhausted
    have endpointVal : endpoint.val = remaining + 1 := count
    obtain ⟨next, exhausted, iteratorNormal, nextCount⟩ := reverse_step endpoint (by omega)
    obtain ⟨previous, subNormal, previousPost⟩ := RawMulTable.normal_of_spec _ _
      (Usize.sub_spec (x := endpoint) (y := 1#usize) (by simp; omega))
    have previousVal : previous.val = remaining := by have := previousPost.1; simp at this; omega
    let updated := words.setAtNat (remaining + 1) (words[remaining]! ^^^ mulWord root words[remaining + 1]!)
    have body : certificate_loop0_loop0.body fieldDictionary kernels root (reverseAt endpoint false) words =
        Result.ok (ControlFlow.cont (reverseAt next exhausted, updated)) := by
      simp only [certificate_loop0_loop0.body, iteratorNormal, bind_ok]
      dsimp! only
      simp only [subNormal, bind_ok, read_normal words previous (by omega),
        read_normal words endpoint (by omega), mul, native_mul_word, lift,
        update_normal words endpoint _ (by omega), previousVal, endpointVal, updated]
      rfl
    have updatedLen : updated.length = words.length := Slice.setAtNat_length _ _ _
    have rest := ih updated next exhausted (by omega) (by rw [updatedLen]; omega)
    unfold certificate_loop0_loop0 loop
    dsimp only
    rw [body]
    simp only [bind_ok]
    exact rest

/-- Exact list-frame output of the native certificate product loop, before comparison. -/
theorem outer_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (mul : NativeMul kernels) (roots words : Slice U64) (index : Usize) (count : Nat)
    (remaining : index.val + count = roots.length) (room : roots.length < words.length) :
    certificate_loop0 fieldDictionary kernels (⟨⟨roots, index.val⟩, index⟩ : RootIterator) words =
      Result.ok (productFrom roots words index.val count) := by
  induction count generalizing index words with
  | zero =>
    obtain ⟨terminal, stop⟩ := root_done roots index (by omega)
    unfold certificate_loop0 loop
    dsimp only
    simp only [certificate_loop0.body, stop, bind_ok]
    dsimp! only
    simp only [bind_ok]
  | succ count ih =>
    obtain ⟨next, read, advanced⟩ := root_next roots index (by omega)
    obtain ⟨stop, plusOne, stopVal⟩ := RawMulTable.normal_of_spec _ _
      (Usize.add_spec (x := index) (y := 1#usize) (by
        have maxBound : words.length ≤ Usize.max := words.length_ineq
        change index.val + 1 ≤ Usize.max
        omega))
    have endVal : stop.val = index.val + 1 := stopVal
    let expanded := words.setAtNat (index.val + 1) words[index.val]!
    let inner := descend roots[index.val]! index.val expanded
    have innerLen : inner.length = words.length := by simp [inner, expanded, Slice.setAtNat_length]
    have innerNormal : certificate_loop0_loop0 fieldDictionary kernels (reverseAt index false)
        expanded roots[index.val]! = Result.ok inner :=
      inner_refines kernels mul roots[index.val]! expanded index false index.val rfl
        (by rw [show expanded.length = words.length from Slice.setAtNat_length _ _ _]; omega)
    have body : certificate_loop0.body fieldDictionary kernels
        (⟨⟨roots, index.val⟩, index⟩ : RootIterator) words =
        Result.ok (ControlFlow.cont ((⟨⟨roots, next.val⟩, next⟩ : RootIterator),
          productStep words roots[index.val]! index.val)) := by
      simp only [certificate_loop0.body, read, bind_ok]
      dsimp! only
      simp only [plusOne, bind_ok, read_normal words index (by omega),
        update_normal words stop _ (by omega), endVal, core.ops.range.RangeInclusive.new,
        core.iter.traits.iterator.Iterator.rev.trait_default, core.iter.traits.iterator.Iterator.rev.default]
      change (do
        let product ← certificate_loop0_loop0 fieldDictionary kernels (reverseAt index false) expanded roots[index.val]!
        let constant ← Slice.index_usize product 0#usize
        let result ← kernels.ArithmeticInst.mul roots[index.val]! constant
        let output ← Slice.update product 0#usize result
        Result.ok (ControlFlow.cont ((⟨⟨roots, next.val⟩, next⟩ : RootIterator), output))) = _
      have zeroBound : (0#usize).val < inner.length := by rw [innerLen]; change 0 < words.length; omega
      simp only [Bind.bind, innerNormal, bind_ok, read_normal inner 0#usize zeroBound,
        mul, native_mul_word, update_normal inner 0#usize _ zeroBound, productStep]
      rfl
    have rest := ih (productStep words roots[index.val]! index.val) next (by omega) (by simpa using room)
    unfold certificate_loop0 loop
    dsimp only
    rw [body]
    simp only [bind_ok]
    change certificate_loop0 fieldDictionary kernels (⟨⟨roots, next.val⟩, next⟩ : RootIterator)
      (productStep words roots[index.val]! index.val) = _
    rw [rest, advanced]
    rfl

end BulksketchBridge.Certificate
