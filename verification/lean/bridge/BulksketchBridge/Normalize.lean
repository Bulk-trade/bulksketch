import BulksketchBridge.NormalizeSpec
import BulksketchBridge.InverseUsing
import BulksketchBridge.Algebra.WordNative

namespace BulksketchBridge.Normalize

open Aeneas Aeneas.Std Aeneas.Std.WP Algebra.Gf64
open bulksketch.backend.contract bulksketch.decode.deg34

private abbrev Range := core.ops.range.Range Usize

private theorem read_normal (words : Slice U64) (index : Usize) (bounded : index.val < words.length) :
    Slice.index_usize words index = Result.ok words[index.val]! := by
  obtain ⟨word, normal, value⟩ := RawMulTable.normal_of_spec _ _ (Slice.index_usize_spec words index bounded)
  rw [normal, value, Slice.getElem!_Nat_eq]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! _ _ bounded)

private theorem write_normal (words : Slice U64) (index : Usize) (word : U64)
    (bounded : index.val < words.length) :
    Slice.update words index word = Result.ok (words.setAtNat index.val word) := by
  obtain ⟨updated, normal, value⟩ := RawMulTable.normal_of_spec _ _ (Slice.update_spec words index word bounded)
  rw [normal, value]
  rfl

private theorem set_same (words : Slice U64) (index : Nat) (word : U64) (inside : index < words.length) :
    (words.setAtNat index word)[index]! = word := by
  rw [Slice.getElem!_Nat_eq]
  exact Slice.getElem!_Nat_setAtNat_eq words index word inside

private theorem set_other (words : Slice U64) (slot index : Nat) (word : U64) (distinct : slot ≠ index) :
    (words.setAtNat slot word)[index]! = words[index]! := by
  simp only [Slice.getElem!_Nat_eq]
  exact Slice.getElem!_Nat_setAtNat_ne words slot index word distinct

/-- The original loop changes exactly the active coefficient interval. -/
private theorem loop_frame {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (cleared : Slice U64) (inverse : U64)
    (range : Range) (factor : Slice U64) (sourceBound : range.«end».val ≤ cleared.length)
    (destBound : range.«end».val ≤ factor.length) :
    ∃ output,
      normalize_loop fieldDictionary kernels range cleared factor inverse = Result.ok output ∧
      output.length = factor.length ∧
      ∀ index, index < factor.length → output[index]! =
        if range.start.val ≤ index ∧ index < range.«end».val then mulWord cleared[index]! inverse else factor[index]! := by
  suffices go : ∀ remaining (range : Range) (factor : Slice U64),
      range.«end».val - range.start.val = remaining →
      range.«end».val ≤ cleared.length → range.«end».val ≤ factor.length →
      ∃ output,
        normalize_loop fieldDictionary kernels range cleared factor inverse = Result.ok output ∧
        output.length = factor.length ∧
        ∀ index, index < factor.length → output[index]! =
          if range.start.val ≤ index ∧ index < range.«end».val then mulWord cleared[index]! inverse else factor[index]!
    from go _ range factor rfl sourceBound destBound
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro range factor count sourceBound destBound
    by_cases active : range.start.val < range.«end».val
    · obtain ⟨⟨option, advanced⟩, next, rfl, nextStart, nextEnd⟩ := RawMulTable.normal_of_spec _ _
        (core.iter.range.IteratorRange.next_Usize_some_spec range active)
      let word := mulWord cleared[range.start.val]! inverse
      let updated := factor.setAtNat range.start.val word
      have updateLength : updated.length = factor.length := Slice.setAtNat_length _ _ _
      have read := read_normal cleared range.start (by omega)
      have multiplied : kernels.ArithmeticInst.mul cleared[range.start.val]! inverse = Result.ok word :=
        (arithmetic.1 _ _).trans (native_mul_word _ _)
      have write : Slice.update factor range.start word = Result.ok updated := write_normal _ _ _ (by omega)
      have body : normalize_loop.body fieldDictionary kernels cleared inverse range factor =
          Result.ok (.cont (advanced, updated)) := by
        simp only [normalize_loop.body, next, bind_ok]
        dsimp! only
        simp only [read, multiplied, write, bind_ok]
      obtain ⟨output, rest, lengthEq, values⟩ := ih (advanced.«end».val - advanced.start.val)
        (by rw [nextStart, nextEnd]; omega) advanced updated rfl
        (by rwa [nextEnd]) (by rwa [nextEnd, updateLength])
      refine ⟨output, ?_, lengthEq.trans updateLength, ?_⟩
      · conv => lhs; unfold normalize_loop loop
        dsimp only
        rw [body]
        simp only [bind_ok]
        exact rest
      · intro index inside
        rw [values index (by rwa [updateLength]), nextStart, nextEnd]
        by_cases atStart : index = range.start.val
        · subst index
          rw [ite_eq_right (by omega), ite_eq_left ⟨Nat.le_refl _, active⟩]
          exact set_same factor range.start.val word inside
        · rw [show updated[index]! = factor[index]! from set_other factor range.start.val index word (Ne.symm atStart)]
          simp only [show (range.start.val + 1 ≤ index ∧ index < range.«end».val) ↔
            (range.start.val ≤ index ∧ index < range.«end».val) by omega]
    · obtain ⟨⟨option, unchanged⟩, next, rfl, _⟩ := RawMulTable.normal_of_spec _ _
        (core.iter.range.IteratorRange.next_Usize_none_spec range (by omega))
      refine ⟨factor, ?_, rfl, ?_⟩
      · unfold normalize_loop loop
        dsimp only
        simp only [normalize_loop.body, next, bind_ok]
        dsimp! only
        simp only [bind_ok]
      · intro index _
        rw [ite_eq_right (by omega)]

@[simp] theorem expected_length (cleared : Slice U64) (s : U64) (degree : Nat) (factor : Slice U64) :
    (expectedOutput cleared s degree factor).length = factor.length := by
  simp [expectedOutput, Slice.length]

theorem expected_word (cleared : Slice U64) (s : U64) (degree : Nat) (factor : Slice U64)
    (index : Nat) (inside : index < factor.length) :
    (expectedOutput cleared s degree factor)[index]! = expectedCoefficient cleared s degree factor index := by
  simp only [expectedOutput, Slice.getElem!_Nat_eq, Slice.from_val]
  rw [← List.Inhabited_getElem_eq_getElem! _ _ (by simpa using inside), List.getElem_ofFn]

/-- The native wrapper uses the verified field inverse, then writes the lower coefficients, syndrome and monic one. -/
theorem normalize_refines : ActualNormalizeReturnsExactFrame := by
  intro K kernels arithmetic cleared s degree factor admitted sourceRoom destRoom denominatorNZ
  have positive : 1 ≤ degree.val := by rcases admitted with equal | equal <;> omega
  have small : degree.val ≤ 4 := by rcases admitted with equal | equal <;> omega
  obtain ⟨last, subtract, lastVal, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := degree) (y := 1#usize) (by simpa using positive))
  have lastValue : last.val = degree.val - 1 := lastVal
  let inverse := DirectTwo.inverseWord cleared[5]!
  have inverseNormal : kernels.ArithmeticInst.inverse cleared[5]! = Result.ok (some inverse) := by
    rw [arithmetic.2, InverseUsing.inverse_refines]
    simp only [Inverse.expectedFieldInverse, ite_eq_right denominatorNZ, inverse, DirectTwo.inverseWord]
  have read : Slice.index_usize cleared 5#usize = Result.ok cleared[5]! :=
    read_normal cleared 5#usize (by change 5 < cleared.length; omega)
  let range : Range := ⟨0#usize, last⟩
  obtain ⟨lower, loopNormal, lowerLen, lowerWords⟩ := loop_frame kernels arithmetic cleared inverse range factor
    (by change last.val ≤ cleared.length; omega) (by change last.val ≤ factor.length; omega)
  let penultimate := lower.setAtNat last.val s
  let final := penultimate.setAtNat degree.val 1#u64
  have penultimateLen : penultimate.length = factor.length := (Slice.setAtNat_length _ _ _).trans lowerLen
  have finalLen : final.length = factor.length := (Slice.setAtNat_length _ _ _).trans penultimateLen
  have writeS : Slice.update lower last s = Result.ok penultimate := write_normal _ _ _ (by omega)
  have writeOne : Slice.update penultimate degree 1#u64 = Result.ok final := write_normal _ _ _ (by omega)
  have normal : normalize fieldDictionary kernels cleared s degree factor = Result.ok final := by
    unfold bulksketch.decode.deg34.normalize
    simp only [read, bind_ok, inverseNormal, core.option.Option.expect, Result.ofOption, subtract]
    change (do
      let lower ← normalize_loop fieldDictionary kernels range cleared factor inverse
      let penultimate ← Slice.update lower last s
      Slice.update penultimate degree 1#u64) = _
    simp only [Bind.bind, loopNormal, writeS, writeOne, bind_ok]
  rw [normal]
  congr 1
  apply Slice.ext_getElem (finalLen.trans (expected_length _ _ _ _).symm)
  intro index leftBound rightBound
  have inside : index < factor.length := by omega
  rw [Slice.getElem_Nat_eq final index leftBound,
    Slice.getElem_Nat_eq (expectedOutput cleared s degree.val factor) index rightBound,
    List.Inhabited_getElem_eq_getElem! final.val index leftBound,
    List.Inhabited_getElem_eq_getElem! (expectedOutput cleared s degree.val factor).val index rightBound,
    ← Slice.getElem!_Nat_eq final index,
    ← Slice.getElem!_Nat_eq (expectedOutput cleared s degree.val factor) index, expected_word _ _ _ _ _ inside]
  by_cases top : index = degree.val
  · subst index
    rw [show final[degree.val]! = 1#u64 from set_same penultimate degree.val 1#u64 (by omega)]
    simp [expectedCoefficient, show ¬degree.val < degree.val - 1 by omega,
      show degree.val ≠ degree.val - 1 by omega]
  · rw [show final[index]! = penultimate[index]! from set_other penultimate degree.val index 1#u64 (Ne.symm top)]
    by_cases pen : index = last.val
    · subst index
      rw [show penultimate[last.val]! = s from set_same lower last.val s (by omega)]
      simp [expectedCoefficient, lastValue]
    · rw [show penultimate[index]! = lower[index]! from set_other lower last.val index s (Ne.symm pen),
        lowerWords index inside]
      have rangeCondition : (range.start.val ≤ index ∧ index < range.«end».val) ↔ index < degree.val - 1 := by
        change (0 ≤ index ∧ index < last.val) ↔ index < degree.val - 1
        omega
      simp only [rangeCondition, expectedCoefficient, ← lastValue, pen, top, ite_false, inverse]

/-- Native normalization has the exact quotient-field coefficient at every slot. -/
theorem normalize_field_coefficients : ActualNormalizeFieldCoefficients := by
  intro K kernels arithmetic cleared s degree factor admitted sourceRoom destRoom denominatorNZ
  refine ⟨expectedOutput cleared s degree.val factor,
    normalize_refines kernels arithmetic cleared s degree factor admitted sourceRoom destRoom denominatorNZ,
    expected_length _ _ _ _, ?_⟩
  intro index inside
  rw [expected_word _ _ _ _ _ inside]
  by_cases low : index < degree.val - 1
  · rw [expectedCoefficient, ite_eq_left low, ite_eq_left low]
    change toField (multiplyWord cleared[index]!.bv (DirectTwo.inverseWord cleared[5]!).bv) = _
    rw [toField_mul]
    exact congrArg (toField cleared[index]!.bv * ·) (wordFieldEquiv.apply_symm_apply _)
  · by_cases pen : index = degree.val - 1
    · simp only [expectedCoefficient, ite_eq_right low, ite_eq_left pen]
    · by_cases top : index = degree.val
      · simp only [expectedCoefficient, ite_eq_right low, ite_eq_right pen, ite_eq_left top]
        exact (show toField (1#u64).bv = 1 from toField_one)
      · simp only [expectedCoefficient, ite_eq_right low, ite_eq_right pen, ite_eq_right top]

end BulksketchBridge.Normalize
