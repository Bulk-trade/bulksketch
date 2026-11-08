import BulksketchBridge.QuarticLoopSpec
import BulksketchBridge.Algebra.WordLaws
import BulksketchBridge.Algebra.WordNative

namespace BulksketchBridge.QuarticLoops

open Aeneas Aeneas.Std Aeneas.Std.WP Algebra.Gf64
open bulksketch.backend.contract bulksketch.decode.deg34

set_option maxHeartbeats 2000000

private abbrev Forward := core.ops.range.Range Usize
private abbrev Reverse := core.iter.adapters.rev.Rev Forward
private def fwd (index : Usize) : Forward := ⟨index, 4#usize⟩
private def rev (endpoint : Usize) : Reverse := ⟨⟨0#usize, endpoint⟩⟩
private abbrev nextForward := core.iter.range.IteratorRange.next core.iter.range.StepUsize
private abbrev nextReverse := core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
  (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)

private theorem read_normal (words : Words) (index : Usize) (bound : index.val < 4) :
    Array.index_usize words index = Result.ok words[index.val]! := by
  have bounded : index.val < words.length := by simpa using bound
  obtain ⟨word, normal, exactWord⟩ := RawMulTable.normal_of_spec _ _
    (Array.index_usize_spec words index bounded)
  rw [normal, exactWord, Array.getElem!_Nat_eq]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! _ _ bounded)

private theorem update_normal (words : Words) (index : Usize) (value : U64) (bound : index.val < 4) :
    Array.update words index value = Result.ok (words.set index value) := by
  have bounded : index.val < words.length := by simpa using bound
  obtain ⟨output, normal, exactWord⟩ := RawMulTable.normal_of_spec _ _
    (Array.update_spec words index value bounded)
  rw [normal, exactWord]

private theorem forward_step {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (mul : NativeMul kernels) (roots prefixes : Words) (index next previous : Usize)
    (advance : nextForward (fwd index) = Result.ok (some index, fwd next))
    (subtract : (index - 1#usize : Result Usize) = Result.ok previous)
    (previousBound : previous.val < 4) (indexBound : index.val < 4) :
    quartic_loop0 fieldDictionary kernels (fwd index) roots prefixes =
      quartic_loop0 fieldDictionary kernels (fwd next) roots
        (prefixes.set index (mulWord prefixes[previous.val]! roots[previous.val]!)) := by
  have body : quartic_loop0.body fieldDictionary kernels roots (fwd index) prefixes =
      Result.ok (ControlFlow.cont (fwd next,
        prefixes.set index (mulWord prefixes[previous.val]! roots[previous.val]!))) := by
    simp only [quartic_loop0.body, advance, bind_ok]
    dsimp! only
    simp only [subtract, bind_ok, read_normal prefixes previous previousBound,
      read_normal roots previous previousBound, mul, native_mul_word, update_normal prefixes index _ indexBound]
    rfl
  conv => lhs; unfold quartic_loop0 loop
  dsimp only
  rw [body]
  simp only [bind_ok]
  rfl

private theorem reverse_step {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (mul : NativeMul kernels) (roots prefixes : Words) (shift inverse : U64) (endpoint index : Usize)
    (advance : nextReverse (rev endpoint) = Result.ok (some index, rev index)) (bound : index.val < 4) :
    quartic_loop1 fieldDictionary kernels (rev endpoint) shift roots prefixes inverse =
      quartic_loop1 fieldDictionary kernels (rev index) shift
        (roots.set index (mulWord prefixes[index.val]! inverse ^^^ shift)) prefixes
        (mulWord inverse roots[index.val]!) := by
  have body : quartic_loop1.body fieldDictionary kernels shift prefixes (rev endpoint) roots inverse =
      Result.ok (ControlFlow.cont (rev index,
        roots.set index (mulWord prefixes[index.val]! inverse ^^^ shift),
        mulWord inverse roots[index.val]!)) := by
    simp only [quartic_loop1.body, advance, bind_ok]
    dsimp! only
    simp only [read_normal roots index bound, read_normal prefixes index bound,
      mul, native_mul_word, lift, update_normal roots index _ bound, bind_ok]
    rfl
  conv => lhs; unfold quartic_loop1 loop
  dsimp only
  rw [body]
  simp only [bind_ok]
  rfl

local macro "simp_forward" : tactic => `(tactic|
  simp [fwd, nextForward, core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked,
    core.clone.CloneUsize, core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt,
    liftFun1, liftFun2, UScalar.max, *])

local macro "simp_reverse" : tactic => `(tactic|
  simp [rev, nextReverse, core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep, core.iter.range.UScalarStep.backward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt, liftFun2])

private theorem forward_done {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots prefixes : Words) :
    quartic_loop0 fieldDictionary kernels (fwd 4#usize) roots prefixes = Result.ok prefixes := by
  have stop : nextForward (fwd 4#usize) = Result.ok (none, fwd 4#usize) := by simp_forward
  unfold quartic_loop0 loop
  dsimp only
  simp only [quartic_loop0.body, stop, bind_ok]
  dsimp! only
  simp only [bind_ok]

private theorem reverse_done {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots prefixes : Words) (shift inverse : U64) :
    quartic_loop1 fieldDictionary kernels (rev 0#usize) shift roots prefixes inverse = Result.ok roots := by
  have stop : nextReverse (rev 0#usize) = Result.ok (none, rev 0#usize) := by simp_reverse
  unfold quartic_loop1 loop
  dsimp only
  simp only [quartic_loop1.body, stop, bind_ok]
  dsimp! only
  simp only [bind_ok]

private theorem subtract_one (index previous : Usize) (successor : index.val = previous.val + 1) :
    (index - 1#usize : Result Usize) = Result.ok previous := by
  obtain ⟨result, normal, value, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := index) (y := 1#usize) (by change 1 ≤ index.val; omega))
  have exactResult : result = previous := by
    apply UScalar.eq_of_val_eq
    change result.val = index.val - 1 at value
    omega
  rw [normal, exactResult]

theorem prefix_products_refines : ActualQuarticPrefixProducts := by
  intro K kernels roots mul
  change quartic_loop0 fieldDictionary kernels (fwd 1#usize) roots _ = _
  rw [forward_step kernels mul roots _ 1#usize 2#usize 0#usize (by rcases System.Platform.numBits_eq with h | h <;> simp_forward) (subtract_one _ _ (by decide)) (by decide) (by decide),
    forward_step kernels mul roots _ 2#usize 3#usize 1#usize (by rcases System.Platform.numBits_eq with h | h <;> simp_forward) (subtract_one _ _ (by decide)) (by decide) (by decide),
    forward_step kernels mul roots _ 3#usize 4#usize 2#usize (by rcases System.Platform.numBits_eq with h | h <;> simp_forward) (subtract_one _ _ (by decide)) (by decide) (by decide),
    forward_done]
  congr 1
  apply (Array.eq_iff _ _).mpr
  have oneMul (word : U64) : mulWord 1#u64 word = word := by
    apply U64.bv_eq_imp_eq
    change multiplyWord 1 word.bv = word.bv
    exact one_multiplyWord _
  simp [prefixes, Array.getElem!_Nat_eq, Array.make, oneMul]

theorem reverse_words_refine : ActualQuarticReverseWords := by
  intro K kernels roots prefixes shift inverse mul
  change quartic_loop1 fieldDictionary kernels (rev 4#usize) shift roots prefixes inverse = _
  rw [reverse_step kernels mul _ prefixes shift _ 4#usize 3#usize (by simp_reverse) (by decide),
    reverse_step kernels mul _ prefixes shift _ 3#usize 2#usize (by simp_reverse) (by decide),
    reverse_step kernels mul _ prefixes shift _ 2#usize 1#usize (by simp_reverse) (by decide),
    reverse_step kernels mul _ prefixes shift _ 1#usize 0#usize (by simp_reverse) (by decide),
    reverse_done]
  congr 1
  apply (Array.eq_iff _ _).mpr
  apply List.ext_getElem (by simp [shiftedReciprocals])
  intro index h1 h2
  have bound : index < 4 := by simpa using h1
  interval_cases index <;> simp [shiftedReciprocals, Array.make]

end BulksketchBridge.QuarticLoops
