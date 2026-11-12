import BulksketchBridge.NativeDeflateSyntheticLoop

namespace BulksketchBridge.Deflation

open Aeneas Aeneas.Std Result DenseCoefficient RebuiltLfsr SliceKernels Algebra.Gf64
open bulksketch.backend.contract bulksketch.decode.stages.Execution
open DenseDivision (reverseRange)

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem prefix_word (words : Slice U64) (length i : Nat) (inside : i < length) :
    (prefixSlice words length)[i]! = words[i]! := by
  simp only [prefixSlice, Slice.getElem!_Nat_eq, Slice.from_val, List.getElem!_eq_getElem?_getD,
    List.getElem?_take_of_lt inside]

private theorem read_word (words : Slice U64) (i : Usize) (fits : i.val < words.length) :
    Slice.index_usize words i = .ok words[i.val]! := by
  obtain ⟨word, normal, value⟩ := RawMulTable.normal_of_spec _ _ (Slice.index_usize_spec words i fits)
  rw [normal, value, Slice.getElem!_Nat_eq]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! words.val i.val fits)

/-- The original top-coefficient write and native inner loop compute the
entire synthetic quotient in the same scratch slice. The remainder
condition then tests the original locator at the candidate root. -/
theorem native_synthetic_step {K : Type} (field : bulksketch.field.BinaryField bulksketch.field.Gf64)
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (mul : ∀ a b, kernels.ArithmeticInst.mul a b = .ok (mulWord a b))
    (locator quotient : Slice U64) (root : U64) (degree : Usize)
    (positive : 0 < degree.val) (locatorRoom : degree.val < locator.length)
    (quotientRoom : degree.val ≤ quotient.length) :
    let seeded := quotient.setAtNat (degree.val - 1) locator[degree.val]!
    let output := syntheticFold locator root (degree.val - 1) seeded
    (do
      let lead ← Slice.index_usize locator degree
      let index ← degree - 1#usize
      let written ← Slice.update quotient index lead
      let iterator ← core.iter.traits.iterator.Iterator.rev.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
        { start := 1#usize, «end» := degree }
      deflate_loop0_loop0 field kernels iterator locator written root) = .ok output ∧
    output.length = quotient.length ∧
    slicePolynomial (prefixSlice locator (degree.val + 1)) =
      (Polynomial.X + Polynomial.C (toField root.bv)) *
        slicePolynomial (prefixSlice output degree.val) +
      Polynomial.C (toField (remainderWord locator output root).bv) ∧
    (remainderWord locator output root = 0#u64 ↔
      (slicePolynomial (prefixSlice locator (degree.val + 1))).IsRoot (toField root.bv)) := by
  let seeded := quotient.setAtNat (degree.val - 1) locator[degree.val]!
  let output := syntheticFold locator root (degree.val - 1) seeded
  have seedLength : seeded.length = quotient.length := Slice.setAtNat_length ..
  have outputLength : output.length = quotient.length :=
    (synthetic_fold_length locator seeded root (degree.val - 1)).trans seedLength
  have run := native_synthetic_loop field kernels mul locator seeded root degree positive (by omega)
    (by rwa [seedLength])
  have math : SyntheticColumns (prefixSlice locator (degree.val + 1)) (prefixSlice output degree.val) root degree.val := by
    refine ⟨positive, ?_, ?_, ?_, ?_⟩
    · rw [prefix_length, Nat.min_eq_left (by omega)]
    · rw [prefix_length, outputLength, Nat.min_eq_left quotientRoom]
    · rw [prefix_word _ _ _ (by omega), prefix_word _ _ _ (by omega)]
      change (syntheticFold locator root (degree.val - 1) seeded)[degree.val - 1]! = _
      rw [synthetic_fold_keeps_high _ _ _ _ _ (Nat.le_refl _)]
      unfold seeded
      simpa only [Slice.getElem!_Nat_eq] using (Slice.getElem!_Nat_setAtNat_eq quotient
        (degree.val - 1) locator[degree.val]! (by omega))
    · intro i before
      rw [prefix_word _ _ _ (by omega), prefix_word _ _ _ (by omega), prefix_word _ _ _ before]
      exact synthetic_fold_columns locator seeded root (degree.val - 1) (by rw [seedLength]; omega) i (by omega)
  have remainder :
      remainderWord (prefixSlice locator (degree.val + 1)) (prefixSlice output degree.val) root =
        remainderWord locator output root := by
    unfold remainderWord
    rw [prefix_word _ _ _ (by omega), prefix_word _ _ _ positive]
  refine ⟨?_, outputLength, ?_, ?_⟩
  · obtain ⟨index, subtracted, indexValue, _⟩ := RawMulTable.normal_of_spec _ _
      (Usize.sub_spec (x := degree) (y := 1#usize) (by change 1 ≤ degree.val; omega))
    change index.val = degree.val - 1 at indexValue
    have written := Reconstruction.update_normal quotient index locator[degree.val]! (by omega)
    have reverse :
        core.iter.traits.iterator.Iterator.rev.trait_default
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
          (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
          { start := 1#usize, «end» := degree } = .ok (reverseRange 1#usize degree) := rfl
    simpa only [read_word locator degree locatorRoom, subtracted, Bind.bind, bind_ok,
      written, indexValue, reverse] using run
  · have identity := synthetic_identity _ _ root degree.val math
    rwa [remainder] at identity
  · have criterion := synthetic_remainder_zero_iff_root _ _ root degree.val math
    rwa [remainder] at criterion

#print axioms native_synthetic_step

end BulksketchBridge.Deflation
