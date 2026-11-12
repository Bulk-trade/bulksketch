import BulksketchBridge.DenseDivisionModel
import BulksketchBridge.DenseReducerAlgebra
import BulksketchBridge.DenseNormalization
import BulksketchBridge.ClosedLeafAdvance
import BulksketchBridge.Algebra.WordNative
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace BulksketchBridge.DenseDivision

open Aeneas.Std Algebra.Gf64 Polynomial BmDiscrepancy DenseCoefficient RebuiltLfsr SliceKernels
open DenseMulConvolutionSpec
open BulksketchProofs.Field
open scoped BigOperators BulksketchBridge.DenseMulReductionSpec

set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

noncomputable def rawPolynomial (raw : Slice Raw) (count : Nat) : Polynomial Field :=
  ∑ i ∈ Finset.range count, monomial i (rawValue raw[i]!)

theorem raw_polynomial_coeff (raw : Slice Raw) (count i : Nat) :
    (rawPolynomial raw count).coeff i = if i < count then rawValue raw[i]! else 0 := by
  classical
  rw [rawPolynomial, finsetSum_coeff]
  by_cases active : i < count
  · rw [ite_eq_left active, Finset.sum_eq_single i, coeff_monomial, ite_eq_left rfl]
    · intro j _ unequal
      rw [coeff_monomial, ite_eq_right unequal]
    · intro missing
      exact (missing (Finset.mem_range.mpr active)).elim
  · rw [ite_eq_right active]
    apply Finset.sum_eq_zero
    intro j member
    have other : j ≠ i := by
      have := Finset.mem_range.mp member
      omega
    rw [coeff_monomial, ite_eq_right other]

private theorem raw_low (word : U64) : rawValue ⟨word, 0#u64⟩ = toField word.bv := by
  change toField (reduceFold64 word.bv 0) = _
  simp [reduceFold64, fold64, overflow64]

private theorem raw_xor (left right : Raw) :
    rawValue (xorProduct left right) = rawValue left + rawValue right := by
  change toField (reduceFold64 (left.lo.bv ^^^ right.lo.bv) (left.hi.bv ^^^ right.hi.bv)) = _
  rw [reduceFold64_xor, toField_xor]
  rfl

theorem update_raw_length (divisor : Slice U64) (factor : U64) (offset top : Nat) (raw : Slice Raw) :
    (updateRaw divisor factor offset top raw).length = raw.length := by
  simp only [updateRaw, Slice.length, Slice.from_val, List.length_ofFn]

theorem update_raw_word (divisor : Slice U64) (factor : U64) (offset top slot : Nat) (raw : Slice Raw)
    (bound : slot < raw.length) :
    (updateRaw divisor factor offset top raw)[slot]! = updateWord divisor factor offset top slot raw[slot]! := by
  simp only [updateRaw, Slice.getElem!_Nat_eq, Slice.from_val]
  rw [← List.Inhabited_getElem_eq_getElem! _ slot (by simpa using bound), List.getElem_ofFn]

theorem update_raw_value (divisor : Slice U64) (factor : U64) (offset top slot : Nat) (raw : Slice Raw)
    (bound : slot < raw.length) :
    rawValue (updateRaw divisor factor offset top raw)[slot]! = rawValue raw[slot]! +
      if offset ≤ slot ∧ slot < top then toField factor.bv * toField divisor[slot - offset]!.bv else 0 := by
  rw [update_raw_word _ _ _ _ _ _ bound]
  unfold updateWord
  by_cases active : offset ≤ slot ∧ slot < top
  · rw [ite_eq_left active, ite_eq_left active]
    by_cases zero : factor = 0#u64
    · rw [ite_eq_left zero, zero, show toField (0#u64 : U64).bv = 0 from toField_zero, zero_mul, add_zero]
    · rw [ite_eq_right zero]
      by_cases one : factor = 1#u64
      · rw [ite_eq_left one, one, show toField (1#u64 : U64).bv = 1 from toField_one, one_mul]
        have rewritten : {raw[slot]! with lo := raw[slot]!.lo ^^^ divisor[slot - offset]!} =
            xorProduct raw[slot]! ⟨divisor[slot - offset]!, 0#u64⟩ := by
          unfold xorProduct
          simp
          apply U64.bv_eq_imp_eq
          exact BitVec.xor_zero.symm
        rw [rewritten, raw_xor, raw_low]
      · rw [ite_eq_right one, raw_xor]
        exact congrArg (rawValue raw[slot]! + ·) (toField_mul factor.bv divisor[slot - offset]!.bv)
  · rw [ite_eq_right active, ite_eq_right active, add_zero]

theorem factor_field (inverse : U64) (raw : Raw) :
    toField (factorWord inverse raw).bv = rawValue raw * toField inverse.bv := by
  unfold factorWord
  by_cases one : inverse = 1#u64
  · rw [ite_eq_left one, one, show toField (1#u64 : U64).bv = 1 from toField_one, mul_one]
    rfl
  · rw [ite_eq_right one]
    exact toField_mul _ _

theorem raw_initial_polynomial (input : Slice U64) (raw : Slice Raw) (room : input.length ≤ raw.length) :
    rawPolynomial (initialRaw input raw) input.length = slicePolynomial input := by
  ext i
  rw [raw_polynomial_coeff, slicePolynomial_coeff]
  by_cases active : i < input.length
  · rw [ite_eq_left active, ite_eq_left active]
    have exactWord : (initialRaw input raw)[i]! = ⟨input[i]!, 0#u64⟩ := by
      unfold initialRaw
      rw [Slice.setSlice!_getElem!_middle _ _ _ _ (by
        rw [Nat.sub_zero, List.length_map]
        exact ⟨Nat.zero_le _, active, Nat.lt_of_lt_of_le active room⟩), Nat.sub_zero,
        List.getElem!_map_eq _ _ _ active, ← Slice.getElem!_Nat_eq]
    rw [exactWord, raw_low]
  · rw [ite_eq_right active, ite_eq_right active]

/-- The ignored outgoing raw slot cancels algebraically against the
high coefficient of the shifted divisor. Only the lower raw prefix
represents the next residual. -/
theorem raw_eliminate (divisor : Slice U64) (factor : U64) (degree offset : Nat) (raw : Slice Raw)
    (shape : divisor.length = degree + 1) (room : degree + offset < raw.length)
    (cancels : toField factor.bv * toField divisor[degree]!.bv = rawValue raw[degree + offset]!) :
    rawPolynomial (updateRaw divisor factor offset (degree + offset) raw) (degree + offset) =
      rawPolynomial raw (degree + offset + 1) + (C (toField factor.bv) * X ^ offset) * slicePolynomial divisor := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  ext i
  rw [raw_polynomial_coeff, coeff_add, raw_polynomial_coeff, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul']
  by_cases low : i < degree + offset
  · rw [ite_eq_left low, ite_eq_left (by omega : i < degree + offset + 1), update_raw_value _ _ _ _ _ _ (by omega)]
    by_cases inside : offset ≤ i
    · rw [ite_eq_left ⟨inside, low⟩, ite_eq_left inside, slicePolynomial_coeff, ite_eq_left (by omega)]
    · rw [ite_eq_right (fun inWindow : offset ≤ i ∧ i < degree + offset => inside inWindow.1),
        ite_eq_right inside, mul_zero]
  · rw [ite_eq_right low, ite_eq_left (by omega : offset ≤ i)]
    by_cases exactTop : i = degree + offset
    · subst i
      rw [ite_eq_left (by omega : degree + offset < degree + offset + 1), Nat.add_sub_cancel,
        slicePolynomial_coeff, ite_eq_left (by omega), cancels, CharTwo.add_self_eq_zero]
    · rw [ite_eq_right (by omega : ¬ i < degree + offset + 1), slicePolynomial_coeff,
        ite_eq_right (by omega : ¬ i - offset < divisor.length), mul_zero, add_zero]

private theorem quotient_write (words : Slice U64) (count offset : Nat) (value : U64)
    (room : count ≤ words.length) (admitted : offset < count) (empty : words[offset]! = 0#u64) :
    slicePolynomial (prefixSlice (words.setAtNat offset value) count) =
      slicePolynomial (prefixSlice words count) + C (toField value.bv) * X ^ offset := by
  ext i
  have kept : count ≤ (words.setAtNat offset value).length := by rwa [Slice.setAtNat_length]
  rw [prefix_coeff _ _ _ kept, coeff_add, prefix_coeff _ _ _ room, coeff_C_mul, coeff_X_pow]
  by_cases active : i < count
  · rw [ite_eq_left active, ite_eq_left active]
    by_cases same : i = offset
    · subst i
      rw [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_eq _ _ _ (by omega), empty,
        show toField (0#u64 : U64).bv = 0 from toField_zero, ite_eq_left rfl, mul_one, zero_add]
    · rw [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (Ne.symm same),
        ← Slice.getElem!_Nat_eq, ite_eq_right same, mul_zero, add_zero]
  · rw [ite_eq_right active, ite_eq_right active, ite_eq_right (by omega : i ≠ offset), mul_zero, add_zero]

/-- Every division pass preserves the dividend decomposition, even
when the original code takes one of the zero or unit shortcuts. -/
theorem step_invariant (input divisor quotient : Slice U64) (raw : Slice Raw) (inverse : U64)
    (degree offset count : Nat) (shape : divisor.length = degree + 1) (room : degree + offset < raw.length)
    (quotientRoom : count ≤ quotient.length) (admitted : offset < count) (empty : quotient[offset]! = 0#u64)
    (inverseLaw : toField inverse.bv * toField divisor[degree]!.bv = 1)
    (invariant : slicePolynomial input = slicePolynomial (prefixSlice quotient count) * slicePolynomial divisor +
      rawPolynomial raw (degree + offset + 1)) :
    let factor := factorWord inverse raw[degree + offset]!
    slicePolynomial input = slicePolynomial (prefixSlice (quotient.setAtNat offset factor) count) *
      slicePolynomial divisor + rawPolynomial (updateRaw divisor factor offset (degree + offset) raw) (degree + offset) := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  let factor := factorWord inverse raw[degree + offset]!
  have cancels : toField factor.bv * toField divisor[degree]!.bv = rawValue raw[degree + offset]! := by
    unfold factor
    rw [factor_field, mul_assoc, inverseLaw, mul_one]
  dsimp only
  rw [quotient_write quotient count offset _ quotientRoom admitted empty,
    raw_eliminate divisor _ degree offset raw shape room cancels, invariant]
  let q := slicePolynomial (prefixSlice quotient count)
  let b := slicePolynomial divisor
  let r := rawPolynomial raw (degree + offset + 1)
  let term := C (toField factor.bv) * X ^ offset * b
  change q * b + r = (q + C (toField factor.bv) * X ^ offset) * b + (r + term)
  calc
    _ = q * b + r + (term + term) := by rw [CharTwo.add_self_eq_zero, add_zero]
    _ = _ := by unfold term; ring

theorem descend_widths (divisor : Slice U64) (degree count : Nat) (inverse : U64)
    (quotient : Slice U64) (raw : Slice Raw) :
    (descend divisor degree inverse count quotient raw).1.length = quotient.length ∧
      (descend divisor degree inverse count quotient raw).2.length = raw.length := by
  induction count generalizing quotient raw with
  | zero => exact ⟨rfl, rfl⟩
  | succ count ih =>
    rw [descend]
    obtain ⟨qLen, rLen⟩ := ih (quotient.setAtNat count (factorWord inverse raw[degree + count]!))
      (updateRaw divisor (factorWord inverse raw[degree + count]!) count (degree + count) raw)
    exact ⟨qLen.trans (Slice.setAtNat_length ..), rLen.trans (update_raw_length ..)⟩

theorem descend_invariant (input divisor quotient : Slice U64) (raw : Slice Raw) (inverse : U64)
    (degree count qCount : Nat) (shape : divisor.length = degree + 1)
    (rawRoom : degree + count ≤ raw.length) (quotientRoom : qCount ≤ quotient.length) (steps : count ≤ qCount)
    (zeroBefore : ∀ i < count, quotient[i]! = 0#u64)
    (inverseLaw : toField inverse.bv * toField divisor[degree]!.bv = 1)
    (invariant : slicePolynomial input = slicePolynomial (prefixSlice quotient qCount) * slicePolynomial divisor +
      rawPolynomial raw (degree + count)) :
    let (q, r) := descend divisor degree inverse count quotient raw
    slicePolynomial input = slicePolynomial (prefixSlice q qCount) * slicePolynomial divisor + rawPolynomial r degree := by
  induction count generalizing quotient raw with
  | zero => simpa only [Nat.add_zero, descend] using invariant
  | succ count ih =>
    let factor := factorWord inverse raw[degree + count]!
    let q := quotient.setAtNat count factor
    let r := updateRaw divisor factor count (degree + count) raw
    have stillZero : ∀ i < count, q[i]! = 0#u64 := by
      intro i below
      change (quotient.setAtNat count factor)[i]! = _
      rw [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (by omega),
        ← Slice.getElem!_Nat_eq, zeroBefore i (by omega)]
    change (let (q', r') := descend divisor degree inverse count q r
            slicePolynomial input = slicePolynomial (prefixSlice q' qCount) * slicePolynomial divisor + rawPolynomial r' degree)
    exact ih q r (by unfold r; rw [update_raw_length]; omega)
      (by unfold q; rwa [Slice.setAtNat_length]) (by omega) stillZero
      (step_invariant input divisor quotient raw inverse degree count qCount shape (by omega)
        quotientRoom (by omega) (zeroBefore count (by omega)) inverseLaw invariant)

private theorem raw_polynomial_degree (raw : Slice Raw) (count : Nat) :
    (rawPolynomial raw count).degree < count := by
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro i outside
  rw [raw_polynomial_coeff, ite_eq_right (Nat.not_lt.mpr outside)]

theorem cleared_length (words : Slice U64) (count : Nat) :
    (cleared words count).length = words.length := restore_length _ _

theorem cleared_word (words : Slice U64) (count i : Nat) (room : count ≤ words.length)
    (active : i < count) : (cleared words count)[i]! = 0#u64 := by
  have prefixLen : (prefixSlice words count).length = count :=
    (prefix_length _ _).trans (Nat.min_eq_left room)
  unfold cleared
  rw [Slice.getElem!_Nat_eq]
  simp only [restorePrefix, zeroWords, Slice.from_val, prefixLen]
  rw [List.getElem!_setSlice!_middle _ _ _ _ (by
      rw [Nat.sub_zero, List.length_replicate]
      exact ⟨Nat.zero_le _, active, Nat.lt_of_lt_of_le active room⟩),
    Nat.sub_zero, List.getElem!_replicate _ active]

private theorem cleared_polynomial (words : Slice U64) (count : Nat) (room : count ≤ words.length) :
    slicePolynomial (prefixSlice (cleared words count) count) = 0 := by
  ext i
  rw [prefix_coeff _ _ _ (by rwa [cleared_length]), coeff_zero]
  by_cases active : i < count
  · rw [ite_eq_left active, cleared_word words count i room active]
    exact toField_zero
  · rw [ite_eq_right active]

theorem remainder_words_length (raw : Slice Raw) (count : Nat) (room : count ≤ raw.length) :
    (remainderWords raw count).length = count := by
  simp only [remainderWords, Slice.length, Slice.from_val, List.length_ofFn, Nat.min_eq_left room]

private theorem remainder_polynomial (raw : Slice Raw) (count : Nat) (room : count ≤ raw.length) :
    slicePolynomial (remainderWords raw count) = rawPolynomial raw count := by
  ext i
  rw [slicePolynomial_coeff, remainder_words_length raw count room, raw_polynomial_coeff]
  by_cases active : i < count
  · rw [ite_eq_left active, ite_eq_left active]
    have value : (remainderWords raw count)[i]! = DenseMulReductionSpec.reduceWord raw[i]! := by
      simp only [remainderWords, Slice.getElem!_Nat_eq, Slice.from_val, Nat.min_eq_left room]
      rw [← List.Inhabited_getElem_eq_getElem! _ i (by simpa only [List.length_ofFn] using active), List.getElem_ofFn]
      rfl
    rw [value]
    rfl
  · rw [ite_eq_right active, ite_eq_right active]

private theorem restored_words (dst patch : Slice U64) (count : Nat)
    (width : patch.length = count) (room : count ≤ dst.length) :
    prefixSlice (restorePrefix dst patch) count = patch := by
  apply Slice.ext
  have patchRoom : patch.val.length ≤ dst.val.length := by change patch.length ≤ dst.length; omega
  have countEq : patch.val.length = count := width
  simp only [prefixSlice, restorePrefix, Slice.from_val, List.setSlice!, List.take_zero,
    List.nil_append, Nat.sub_zero, Nat.zero_add, Nat.min_eq_left patchRoom, List.take_length]
  rw [← countEq, List.take_left]

theorem normalized_value (words : Slice U64) (count : Nat) (room : count ≤ words.length) :
    (DenseReducerSquare.outputLength words count).val = DenseNormalization.normalizedLength (words.val.take count) := by
  simp only [DenseReducerSquare.outputLength, prefixSlice, Slice.from_val]
  have bound := DenseNormalization.normalizedLength_le (words.val.take count)
  have length : (words.val.take count).length ≤ count := by simp [List.length_take]
  exact ClosedLeafAdvance.word_val _ (by
    have size : words.length ≤ Usize.max := words.length_ineq
    omega)

theorem expected_widths (a b q rem : Slice U64) (raw : Slice Raw) (inverse : U64) :
    let out := expectedDivRem a b q rem raw inverse
    out.2.1.length = q.length ∧ out.2.2.1.length = rem.length ∧ out.2.2.2.length = raw.length := by
  simp only [expectedDivRem]
  have ⟨quotientLen, rawLen⟩ := descend_widths b (b.length - 1) (a.length - (b.length - 1)) inverse
    (cleared q (a.length + 1)) (initialRaw a raw)
  simp only [cleared_length, initialRaw, Slice.setSlice!_length] at quotientLen rawLen
  exact ⟨quotientLen, (restore_length _ _).trans (cleared_length ..), rawLen⟩

/-- The raw descending schedule returns normalized words for a
quotient/remainder decomposition with strict degree descent. -/
theorem model_meaning (a b q rem : Slice U64) (raw : Slice Raw) (inverse : U64)
    (divisorPositive : 0 < b.length) (qRoom : a.length + 1 ≤ q.length)
    (remRoom : a.length + 1 ≤ rem.length) (rawRoom : a.length + 1 ≤ raw.length)
    (inverseLaw : toField inverse.bv * toField b[b.length - 1]!.bv = 1) :
    let out := expectedDivRem a b q rem raw inverse
    let quotient := slicePolynomial (prefixSlice out.2.1 out.1.1.val)
    let remainder := slicePolynomial (prefixSlice out.2.2.1 out.1.2.val)
    slicePolynomial a = quotient * slicePolynomial b + remainder ∧
      remainder.degree < (slicePolynomial b).degree := by
  let size := a.length + 1
  let degree := b.length - 1
  let remCount := min degree a.length
  let startQ := cleared q size
  let startRaw := initialRaw a raw
  let out := descend b degree inverse (a.length - degree) startQ startRaw
  let remainder := restorePrefix (cleared rem size) (remainderWords out.2 remCount)
  have shape : b.length = degree + 1 := by unfold degree; omega
  have startRawLen : startRaw.length = raw.length := Slice.setSlice!_length ..
  have startQZero := cleared_polynomial q size qRoom
  have startR := raw_initial_polynomial a raw (by omega)
  have ⟨outQLen, outRawLen⟩ := descend_widths b degree (a.length - degree) inverse startQ startRaw
  have dec : slicePolynomial a = slicePolynomial (prefixSlice out.1 size) * slicePolynomial b +
      rawPolynomial out.2 remCount := by
    by_cases steps : degree ≤ a.length
    · have top := Nat.add_sub_of_le steps
      have startInv : slicePolynomial a = slicePolynomial (prefixSlice startQ size) *
          slicePolynomial b + rawPolynomial startRaw (degree + (a.length - degree)) := by
        rw [top, startQZero, zero_mul, zero_add, startR]
      rw [show remCount = degree by exact Nat.min_eq_left steps]
      have countRoom : degree + (a.length - degree) ≤ startRaw.length := by omega
      exact descend_invariant a b startQ startRaw inverse degree (a.length - degree) size shape countRoom
        (by rw [cleared_length]; exact qRoom) (by omega)
        (fun i hi => cleared_word q size i qRoom (by omega)) inverseLaw startInv
    · have noSteps : a.length - degree = 0 := by omega
      change slicePolynomial a = slicePolynomial (prefixSlice (descend b degree inverse (a.length - degree) startQ startRaw).1 size) *
        slicePolynomial b + rawPolynomial (descend b degree inverse (a.length - degree) startQ startRaw).2 remCount
      rw [noSteps, descend, show remCount = a.length by exact Nat.min_eq_right (by omega), startQZero,
        zero_mul, zero_add, startR]
  have bDegree : (slicePolynomial b).degree = degree := by
    have lead : (slicePolynomial b).coeff degree ≠ 0 := by
      rw [slicePolynomial_coeff, ite_eq_left (by omega)]
      intro bad
      rw [bad, mul_zero] at inverseLaw
      exact zero_ne_one inverseLaw
    have upper : (slicePolynomial b).natDegree ≤ degree := by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro i hi
      rw [slicePolynomial_coeff, ite_eq_right (by omega)]
    have nonzero : slicePolynomial b ≠ 0 := by
      intro h
      exact lead (by rw [h, coeff_zero])
    rw [degree_eq_natDegree nonzero, natDegree_eq_of_le_of_coeff_ne_zero upper lead]
  have remainderRoom : remCount ≤ out.2.length := by rw [outRawLen, startRawLen]; unfold remCount; omega
  have qBound : size ≤ out.1.length := by rw [outQLen, cleared_length]; exact qRoom
  have rBound : remCount ≤ remainder.length := by
    change remCount ≤ (restorePrefix (cleared rem size) _).length
    rw [restore_length, cleared_length]
    unfold remCount
    omega
  have qNorm : slicePolynomial (prefixSlice out.1 (DenseReducerSquare.outputLength out.1 size).val) =
      slicePolynomial (prefixSlice out.1 size) := by
    rw [normalized_value _ _ qBound, normalized_prefix_polynomial _ _ qBound]
  have rNorm : slicePolynomial (prefixSlice remainder (DenseReducerSquare.outputLength remainder remCount).val) =
      rawPolynomial out.2 remCount := by
    rw [normalized_value _ _ rBound, normalized_prefix_polynomial _ _ rBound]
    have remRoom' : remCount ≤ (cleared rem size).length := by rw [← restore_length _ (remainderWords out.2 remCount)]; exact rBound
    change slicePolynomial (prefixSlice (restorePrefix (cleared rem size) (remainderWords out.2 remCount)) remCount) = _
    rw [restored_words _ _ _ (remainder_words_length _ _ remainderRoom) remRoom',
      remainder_polynomial _ _ remainderRoom]
  change slicePolynomial a =
      slicePolynomial (prefixSlice out.1 (DenseReducerSquare.outputLength out.1 size).val) * slicePolynomial b +
        slicePolynomial (prefixSlice remainder (DenseReducerSquare.outputLength remainder remCount).val) ∧
      (slicePolynomial (prefixSlice remainder (DenseReducerSquare.outputLength remainder remCount).val)).degree <
        (slicePolynomial b).degree
  rw [qNorm, rNorm, bDegree]
  exact ⟨dec, (raw_polynomial_degree _ _).trans_le (by exact_mod_cast Nat.min_le_left degree a.length)⟩

end BulksketchBridge.DenseDivision
