import BulksketchBridge.QuarticControlSpec
import BulksketchBridge.QuarticLoop
import BulksketchBridge.AffineQuartic
import BulksketchBridge.Cubic

namespace BulksketchBridge.QuarticControl

open Aeneas Aeneas.Std Aeneas.Std.WP Algebra.Gf64
open bulksketch.backend.contract bulksketch.decode.deg34
open bulksketch.core.option.Option.Insts

private theorem slice_read (words : Slice U64) (index : Usize) (bounded : index.val < words.length) :
    Slice.index_usize words index = Result.ok words[index.val]! := by
  obtain ⟨value, normal, exactWord⟩ := RawMulTable.normal_of_spec _ _ (Slice.index_usize_spec words index bounded)
  rw [normal, exactWord, Slice.getElem!_Nat_eq]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! _ _ bounded)

private theorem array_last (words : Words) :
    Array.index_usize words 3#usize = Result.ok words[3]! := by
  have bounded : (3#usize : Usize).val < words.length := by simp
  obtain ⟨word, normal, exactWord⟩ := RawMulTable.normal_of_spec _ _
    (Array.index_usize_spec words 3#usize bounded)
  rw [normal, exactWord, Array.getElem!_Nat_eq]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! _ _ bounded)

private theorem contains_exact (words : Slice U64) (word : U64) :
    core.slice.Slice.contains core.cmp.PartialEqU64 words word = Result.ok (decide (word ∈ words.val)) := by
  unfold core.slice.Slice.contains
  induction words.val with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.anyM_cons, liftFun2, core.cmp.impls.PartialEqU64.eq, ih, List.mem_cons]
    by_cases same : word = head <;> simp [same, pure, Bind.bind]

private theorem reverse_range :
    core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
      ⟨0#usize, 4#usize⟩ = Result.ok ⟨⟨0#usize, 4#usize⟩⟩ := rfl

/-- Every original quartic branch returns exactly the checked dispatch result. -/
theorem quartic_refines : ActualQuarticReturnsExact := by
  intro K kernels factor arithmetic bound
  let a := factor[3]!
  let b := factor[2]!
  let c := factor[1]!
  let d := factor[0]!
  have read0 : Slice.index_usize factor 0#usize = Result.ok d :=
    slice_read factor 0#usize (by change 0 < factor.length; omega)
  have read1 : Slice.index_usize factor 1#usize = Result.ok c :=
    slice_read factor 1#usize (by change 1 < factor.length; omega)
  have read2 : Slice.index_usize factor 2#usize = Result.ok b :=
    slice_read factor 2#usize (by change 2 < factor.length; omega)
  have read3 : Slice.index_usize factor 3#usize = Result.ok a :=
    slice_read factor 3#usize (by change 3 < factor.length; omega)
  change match prepare a b c d with
    | none => quartic fieldDictionary kernels factor = Result.ok none
    | some (.direct b c d) => ∃ output,
        affine_quartic fieldDictionary kernels b c d = Result.ok output ∧
        quartic fieldDictionary kernels factor = Result.ok output
    | some (.shifted b c d shift) => ∃ output,
        affine_quartic fieldDictionary kernels b c d = Result.ok output ∧
        quartic fieldDictionary kernels factor = Result.ok (finish shift output)
  by_cases aZero : a = 0#u64
  · obtain ⟨output, normal, _, _⟩ := AffineQuartic.affine_quartic_refines kernels b c d arithmetic
    simp only [prepare, aZero, ite_true]
    refine ⟨output, normal, ?_⟩
    simpa only [quartic, read3, read2, read1, read0, bind_ok, aZero, ite_true] using normal
  · have mulNormal (x y : U64) : kernels.ArithmeticInst.mul x y = Result.ok (mulWord x y) :=
      (arithmetic.1.1 x y).trans (native_mul_word x y)
    have squareNormal (x : U64) : kernels.ArithmeticInst.square x = Result.ok (squareWord x) :=
      (arithmetic.1.2.1 x).trans (Square.square_refines x)
    have frobeniusNormal (x : U64) (count : U32) :
        kernels.ArithmeticInst.frobenius x count = Result.ok (frobeniusWord x count) :=
      (arithmetic.1.2.2 x count).trans (FrobeniusPeriod.native_unmodded_refines x count)
    have inverseNormal (x : U64) : kernels.ArithmeticInst.inverse x = Result.ok (Inverse.expectedFieldInverse x) := by
      rw [arithmetic.2.1, InverseUsing.inverse_refines]
    have aInverse : kernels.ArithmeticInst.inverse a = Result.ok (some (inverseWord a)) :=
      Cubic.inverse_normal kernels arithmetic a aZero
    let shift := shiftWord (mulWord c (inverseWord a))
    let denominator := denominatorWord b d shift
    have shiftEq : squareWord (frobeniusWord (frobeniusWord (mulWord c (inverseWord a)) 31#u32) 31#u32) = shift := rfl
    have denominatorEq : squareWord (squareWord shift) ^^^ mulWord b (squareWord shift) ^^^ d = denominator := rfl
    by_cases denomZero : denominator = 0#u64
    · simp only [prepare, aZero, ite_false, show shiftWord (mulWord c (inverseWord a)) = shift from rfl,
        show denominatorWord b d shift = denominator from rfl, denomZero, ite_true]
      simp only [quartic, read3, read2, read1, read0, bind_ok, aZero, ite_false, aInverse,
        CoreOpsTry_traitTry.branch, mulNormal, frobeniusNormal, squareNormal, shiftEq, lift,
        denominatorEq, denomZero, ite_true]
    · let inverse := inverseWord denominator
      have denomInverse : kernels.ArithmeticInst.inverse denominator = Result.ok (some inverse) :=
        Cubic.inverse_normal kernels arithmetic denominator denomZero
      let transformedB := mulWord (b ^^^ mulWord a shift) inverse
      let transformedC := mulWord a inverse
      obtain ⟨output, normal, _, _⟩ := AffineQuartic.affine_quartic_refines kernels transformedB transformedC inverse arithmetic
      simp only [prepare, aZero, ite_false, show shiftWord (mulWord c (inverseWord a)) = shift from rfl,
        show denominatorWord b d shift = denominator from rfl, denomZero, transformedCoefficients]
      refine ⟨output, normal, ?_⟩
      simp only [quartic, read3, read2, read1, read0, bind_ok, aZero, ite_false, aInverse,
        CoreOpsTry_traitTry.branch, mulNormal, frobeniusNormal, squareNormal, shiftEq, lift,
        denominatorEq, denomZero, denomInverse,
        show mulWord (b ^^^ mulWord a shift) inverse = transformedB from rfl,
        show mulWord a inverse = transformedC from rfl, normal]
      cases output with
      | none => rfl
      | some roots =>
        have prefixNormal := QuarticLoops.prefix_products_refines kernels roots arithmetic.1.1
        simp only [bind_ok, finish, contains_exact, Array.val_to_slice]
        change (if decide (0#u64 ∈ roots.val) then Result.ok none else _) =
          Result.ok (if 0#u64 ∈ roots.val then none else _)
        by_cases zero : 0#u64 ∈ roots.val
        · simp only [zero, decide_true, ite_true]
        · simp only [zero, decide_false, Bool.false_eq_true, ite_false, prefixNormal, array_last,
            inverseNormal, bind_ok]
          cases Inverse.expectedFieldInverse (mulWord (QuarticLoops.prefixes roots)[3]! roots[3]!) with
          | none => rfl
          | some inverseProduct =>
            simp only [bind_ok, reverse_range,
              QuarticLoops.reverse_words_refine kernels roots (QuarticLoops.prefixes roots) shift
                inverseProduct arithmetic.1.1]
            rfl

end BulksketchBridge.QuarticControl
