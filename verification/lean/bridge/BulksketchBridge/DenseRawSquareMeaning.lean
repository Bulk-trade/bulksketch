import BulksketchBridge.DenseReducerAlgebra
import BulksketchBridge.DenseMulPolynomial
import BulksketchBridge.BmDiscrepancy

namespace BulksketchBridge.DenseRawSquareMeaning

open Aeneas.Std BulksketchBridge Algebra.Gf64 Polynomial
open SliceKernels DenseReducerAlgebra BmDiscrepancy DenseMulConvolutionSpec MutableZip
open DenseCoefficient RebuiltLfsr
open BulksketchProofs.Field
open scoped BigOperators BulksketchBridge.DenseMulReductionSpec

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

def update (table : Slice U64) (degree index : Nat) (coefficient : U64) (raw : Slice Raw) : Slice Raw :=
  let square := Square.expectedWord coefficient
  if index < firstHigh degree then
    let old := raw[2 * index]!
    raw.setAtNat (2 * index) { old with lo := old.lo ^^^ square }
  else
    mapFrom raw (tableRow table degree (index - firstHigh degree))
      (fun old entry => xorProduct old (RawMul.expectedProduct square entry)) 0

def accumulate (input table : Slice U64) (degree : Nat) (raw : Slice Raw)
    (index : Nat) : Nat → Slice Raw
  | 0 => raw
  | count + 1 => accumulate input table degree (update table degree index input[index]! raw) (index + 1) count

theorem update_length (table : Slice U64) (degree index : Nat) (coefficient : U64) (raw : Slice Raw) :
    (update table degree index coefficient raw).length = raw.length := by
  unfold update
  split <;> simp only [Slice.setAtNat_length, mapFrom_length]

private theorem raw_xor (left right : Raw) : rawValue (xorProduct left right) = rawValue left + rawValue right := by
  change toField (reduceFold64 (left.lo.bv ^^^ right.lo.bv) (left.hi.bv ^^^ right.hi.bv)) = _
  rw [reduceFold64_xor, toField_xor]
  rfl

private theorem raw_low (word : U64) : rawValue ⟨word, 0#u64⟩ = toField word.bv := by
  change toField (reduceFold64 word.bv 0) = _
  simp [reduceFold64, fold64, overflow64]

private noncomputable def term (input table : Slice U64) (degree index slot : Nat) : Field :=
  (C ((slicePolynomial input).coeff index ^ 2) *
    (if index < firstHigh degree then X ^ (2 * index) else
      slicePolynomial (tableRow table degree (index - firstHigh degree)))).coeff slot

theorem update_value (input modulus table : Slice U64) (degree index slot : Nat) (raw : Slice Raw)
    (bounded : index < input.length) (inputBound : input.length ≤ degree)
    (valid : CorrectTable modulus table degree) (rawWidth : raw.length = degree) (active : slot < degree) :
    rawValue (update table degree index input[index]! raw)[slot]! =
      rawValue raw[slot]! + term input table degree index slot := by
  let squared := Square.expectedWord input[index]!
  have fieldSquare : toField squared.bv = (slicePolynomial input).coeff index ^ 2 := by
    rw [slicePolynomial_coeff, ite_eq_left bounded]
    exact toField_square input[index]!.bv
  by_cases low : index < firstHigh degree
  · have destination : 2 * index < degree := by unfold firstHigh at low; omega
    simp only [update, low, ite_true, term, coeff_C_mul, coeff_X_pow]
    by_cases same : slot = 2 * index
    · subst slot
      rw [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_eq _ _ _ (by omega)]
      have exactRaw : { raw[2 * index]! with lo := raw[2 * index]!.lo ^^^ squared } =
          xorProduct raw[2 * index]! ⟨squared, 0#u64⟩ := by
        unfold xorProduct
        simp
        apply U64.bv_eq_imp_eq
        exact BitVec.xor_zero.symm
      rw [exactRaw, raw_xor, raw_low, fieldSquare, ite_eq_left rfl, mul_one]
    · rw [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (Ne.symm same),
        ← Slice.getElem!_Nat_eq, ite_eq_right same, mul_zero, add_zero]
  · have highBound : index - firstHigh degree < degree / 2 := by unfold firstHigh at *; omega
    have rowLen := table_row_length modulus table degree _ valid highBound
    simp only [update, low, ite_false, term, coeff_C_mul]
    rw [mapFrom_word _ _ _ _ _ (by omega), ite_eq_left (Nat.zero_le _), raw_xor]
    rw [show rawValue (RawMul.expectedProduct squared (tableRow table degree (index - firstHigh degree))[slot]!) =
      toField squared.bv * toField (tableRow table degree (index - firstHigh degree))[slot]!.bv from toField_mul _ _]
    rw [fieldSquare]
    have coefficient := slicePolynomial_coeff (tableRow table degree (index - firstHigh degree)) slot
    rw [rowLen, ite_eq_left active] at coefficient
    rw [coefficient]

theorem accumulated_value (input modulus table : Slice U64) (degree slot : Nat) (raw : Slice Raw)
    (index count : Nat) (bounded : index + count ≤ input.length) (inputBound : input.length ≤ degree)
    (valid : CorrectTable modulus table degree) (width : raw.length = degree) (active : slot < degree) :
    rawValue (accumulate input table degree raw index count)[slot]! =
      rawValue raw[slot]! + ∑ i ∈ Finset.range count, term input table degree (index + i) slot := by
  induction count generalizing raw index with
  | zero => simp [accumulate]
  | succ count ih =>
    have shifted :
        (∑ i ∈ Finset.range count, term input table degree (index + 1 + i) slot) =
          ∑ i ∈ Finset.range count, term input table degree (index + (i + 1)) slot := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun j => term input table degree j slot) (by omega)
    rw [accumulate, ih _ _ (by omega) (by rw [update_length]; exact width),
      update_value input modulus table degree index slot raw (by omega) inputBound valid width active,
      shifted, Finset.sum_range_succ']
    simp only [Nat.add_zero]
    ac_rfl

/-- After the source-shaped scan starts at zero, each reduced raw slot
is exactly the corresponding coefficient of the table-reduced square. -/
theorem coefficient_meaning (input modulus table : Slice U64) (degree slot : Nat) (raw : Slice Raw)
    (inputBound : input.length ≤ degree) (valid : CorrectTable modulus table degree)
    (width : raw.length = degree) (active : slot < degree) (initial : raw[slot]! = ⟨0#u64, 0#u64⟩) :
    rawValue (accumulate input table degree raw 0 input.length)[slot]! =
      (reduceSquare input table degree).coeff slot := by
  rw [accumulated_value input modulus table degree slot raw 0 input.length (by omega) inputBound valid width active,
    initial, raw_low, show toField (0#u64 : U64).bv = 0 from toField_zero, zero_add, reduceSquare,
    finsetSum_coeff]
  simp only [Nat.zero_add, term]

/-- Exact reduced destination words characterize the monic remainder,
including the shorter normalized prefix exposed to the trace loop. -/
theorem normalized_output (input modulus table output : Slice U64) (degree : Nat) (raw : Slice Raw)
    (modulusShape : modulus.length = degree + 1) (monic : modulus[degree]! = 1#u64)
    (inputBound : input.length ≤ degree) (valid : CorrectTable modulus table degree)
    (width : raw.length = degree) (outputRoom : degree ≤ output.length)
    (zero : ∀ i < degree, raw[i]! = ⟨0#u64, 0#u64⟩)
    (reduced : ∀ i < degree,
      toField output[i]!.bv = rawValue (accumulate input table degree raw 0 input.length)[i]!) :
    slicePolynomial (DenseCoefficient.prefixSlice output
      (DenseNormalization.normalizedLength (output.val.take degree))) =
      (slicePolynomial input ^ 2) %ₘ slicePolynomial modulus := by
  rw [DenseCoefficient.normalized_prefix_polynomial output degree outputRoom,
    ← square_remainder input modulus table degree modulusShape monic inputBound valid]
  ext i
  rw [DenseCoefficient.prefix_coeff output degree i outputRoom]
  by_cases active : i < degree
  · rw [ite_eq_left active, reduced i active,
      coefficient_meaning input modulus table degree i raw inputBound valid width active (zero i active)]
  · rw [ite_eq_right active]
    exact ((degree_lt_iff_coeff_zero _ _).mp (square_degree input modulus table degree inputBound valid)
      i (by omega)).symm

/-- The original reduction loop map and prefix restoration write exactly
the coefficient model used by normalized_output. -/
theorem reduced_destination (input modulus table dst : Slice U64) (degree : Nat) (raw : Slice Raw)
    (shape : modulus.length = degree + 1) (monic : modulus[degree]! = 1#u64)
    (inputRoom : input.length ≤ degree) (valid : CorrectTable modulus table degree)
    (width : raw.length = degree) (destinationRoom : degree ≤ dst.length)
    (zero : ∀ i < degree, raw[i]! = ⟨0#u64, 0#u64⟩) :
    let acc := accumulate input table degree raw 0 input.length
    let reduced := mapFrom (prefixSlice dst degree) acc (fun _ word => BulksketchBridge.DenseMulReductionSpec.reduceWord word) 0
    let output := restorePrefix dst reduced
    output.length = dst.length ∧
      slicePolynomial (prefixSlice output (DenseNormalization.normalizedLength (output.val.take degree))) =
        (slicePolynomial input ^ 2) %ₘ slicePolynomial modulus := by
  let acc := accumulate input table degree raw 0 input.length
  let front := prefixSlice dst degree
  let reduced := mapFrom front acc (fun _ word => BulksketchBridge.DenseMulReductionSpec.reduceWord word) 0
  let output := restorePrefix dst reduced
  have frontLen : front.length = degree := (prefix_length _ _).trans (Nat.min_eq_left destinationRoom)
  have reducedLen : reduced.length = degree := (mapFrom_length _ _ _ _).trans frontLen
  have outputLen : output.length = dst.length := restore_length dst reduced
  refine ⟨outputLen, normalized_output input modulus table output degree raw shape monic inputRoom valid
    width (by omega) zero ?_⟩
  intro i active
  have cell : output[i]! = reduced[i]! := by
    simp only [output, restorePrefix, Slice.getElem!_Nat_eq, Slice.from_val]
    have fit : i < dst.val.length := by change i < dst.length; omega
    have inPatch : i - 0 < reduced.val.length := by
      change i - 0 < reduced.length
      omega
    rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨Nat.zero_le _, inPatch, fit⟩, Nat.sub_zero]
  rw [cell]
  change toField (mapFrom front acc (fun _ word => BulksketchBridge.DenseMulReductionSpec.reduceWord word) 0)[i]!.bv = _
  rw [mapFrom_word _ _ _ _ _ (by omega), ite_eq_left (Nat.zero_le _)]
  rfl

end BulksketchBridge.DenseRawSquareMeaning
