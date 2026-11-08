import BulksketchBridge.DenseMul
import BulksketchBridge.DenseMulCoefficients
import BulksketchBridge.DenseCoefficientPolynomial
import BulksketchBridge.Algebra.WordNative

namespace BulksketchBridge.DenseMul

open Aeneas.Std BulksketchBridge.Algebra.Gf64 BulksketchProofs.Field
open DenseMulConvolutionSpec
open DenseMulReductionSpec (reduceWord)
open SliceKernels DenseCoefficient MutableZip
open scoped BigOperators BulksketchBridge.DenseMulReductionSpec

private noncomputable def rawValue (product : Raw) : Field :=
  toField (reduceWord product).bv

private theorem raw_xor (left right : Raw) :
    rawValue (xorProduct left right) = rawValue left + rawValue right := by
  change toField (reduceFold64 (left.lo.bv ^^^ right.lo.bv) (left.hi.bv ^^^ right.hi.bv)) = _
  rw [reduceFold64_xor, toField_xor]
  rfl

private theorem raw_zero : rawValue zeroProduct = 0 := by
  change toField (reduceFold64 0 0) = 0
  simp [reduceFold64, fold64, overflow64]
  exact toField_zero

private theorem row_value (a b : Slice U64) (raw : Raw) (left slot : Nat) :
    rawValue (rowWord a[left]! b raw left slot) = rawValue raw + contribution a b left slot := by
  by_cases inside : left ≤ slot ∧ slot < left + b.length
  · have bounded : left ≤ slot ∧ slot - left < b.length := by omega
    rw [rowWord, ite_eq_left inside, raw_xor, contribution, ite_eq_left bounded]
    exact congrArg (rawValue raw + ·) (toField_mul a[left]!.bv b[slot - left]!.bv)
  · have outside : ¬ (left ≤ slot ∧ slot - left < b.length) := by omega
    simp only [rowWord, inside, contribution, outside, ite_false, add_zero]

private theorem accumulated_value (a b : Slice U64) (raw : Slice Raw)
    (start count slot : Nat) (bounded : slot < raw.length) :
    rawValue (accumulateRows a b raw start count)[slot]! =
      rawValue raw[slot]! + ∑ i ∈ Finset.range count, contribution a b (start + i) slot := by
  induction count generalizing start raw with
  | zero => simp [accumulateRows]
  | succ count ih =>
    have shifted :
        (∑ i ∈ Finset.range count, contribution a b (start + 1 + i) slot) =
          ∑ i ∈ Finset.range count, contribution a b (start + (i + 1)) slot := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show start + 1 + i = start + (i + 1) by omega]
    rw [accumulateRows, ih _ _ (by simpa using bounded), row_word _ _ _ _ _ bounded, row_value,
      Finset.sum_range_succ', Nat.add_zero, shifted]
    ac_rfl

@[simp] theorem finished_raw_length (a b : Slice U64) (raw : Slice Raw) :
    (finishedRaw a b raw).length = raw.length := by simp [finishedRaw, clearedRaw]

@[simp] theorem finished_dst_length (a b dst : Slice U64) (raw : Slice Raw) :
    (finishedDst a b dst raw).length = dst.length := by simp [finishedDst]

private theorem cleared_word (raw : Slice Raw) (len slot : Nat)
    (active : slot < len) (bounded : slot < raw.length) :
    (clearedRaw raw len)[slot]! = zeroProduct := by
  unfold clearedRaw
  rw [Slice.setSlice!_getElem!_middle _ _ _ _ (by simp [active, bounded]), Nat.sub_zero]
  simp [active]

private theorem finished_raw_value (a b : Slice U64) (raw : Slice Raw) (slot : Nat)
    (bounded : slot < raw.length) (active : slot < a.length + b.length - 1) :
    rawValue (finishedRaw a b raw)[slot]! = (slicePolynomial a * slicePolynomial b).coeff slot := by
  rw [finishedRaw, accumulated_value _ _ _ _ _ _ (by simpa [clearedRaw] using bounded),
    cleared_word _ _ _ active bounded, raw_zero, zero_add, coeff_product]
  simp only [Nat.zero_add]

theorem finished_raw_tail (a b : Slice U64) (raw : Slice Raw) (slot : Nat)
    (outside : a.length + b.length - 1 ≤ slot) (bounded : slot < raw.length) :
    (finishedRaw a b raw)[slot]! = raw[slot]! := by
  rw [finishedRaw, accumulate_frame _ _ _ _ _ _ (by simpa [clearedRaw] using bounded) (by omega)]
  exact Slice.setSlice!_getElem!_suffix _ _ _ _ (by simpa using outside)

set_option maxHeartbeats 1000000 in
theorem finished_dst_word (a b dst : Slice U64) (raw : Slice Raw) (slot : Nat)
    (room : a.length + b.length ≤ dst.length) (bounded : slot < dst.length) :
    (finishedDst a b dst raw)[slot]! =
      if slot < a.length + b.length - 1 then reduceWord (finishedRaw a b raw)[slot]! else dst[slot]! := by
  let len := a.length + b.length - 1
  have dstBound : len ≤ dst.length := by omega
  let output := mapFrom (takeSlice dst len) (takeSlice (finishedRaw a b raw) len) (fun _ p => reduceWord p) 0
  have length : output.val.length = len := by
    change output.length = len
    simp [output, Nat.min_eq_left dstBound]
  change (dst.setSlice! 0 output.val)[slot]! =
    if slot < len then reduceWord (finishedRaw a b raw)[slot]! else dst[slot]!
  by_cases active : slot < len
  · have inside : slot < (takeSlice dst len).length := by simpa [Nat.min_eq_left dstBound] using active
    have word := mapFrom_word (takeSlice dst len) (takeSlice (finishedRaw a b raw) len)
      (fun _ p => reduceWord p) 0 slot inside
    rw [ite_eq_left active, Slice.setSlice!_getElem!_middle _ _ _ _ (by simp [length, active, bounded]),
      Nat.sub_zero, ← Slice.getElem!_Nat_eq]
    change output[slot]! = _
    rw [word, ite_eq_left (Nat.zero_le _), take_word _ _ _ active]
  · have outside : 0 + output.val.length ≤ slot := by rw [Nat.zero_add, length]; omega
    rw [ite_eq_right active, Slice.setSlice!_getElem!_suffix _ _ _ _ outside]


theorem finished_dst_product (a b dst : Slice U64) (raw : Slice Raw)
    (dstRoom : a.length + b.length ≤ dst.length) (rawRoom : a.length + b.length ≤ raw.length) :
    slicePolynomial (prefixSlice (finishedDst a b dst raw) (a.length + b.length - 1)) =
      slicePolynomial a * slicePolynomial b := by
  ext slot
  rw [prefix_coeff _ _ _ (by simpa using Nat.le_trans (Nat.sub_le _ _) dstRoom)]
  by_cases active : slot < a.length + b.length - 1
  · rw [ite_eq_left active, finished_dst_word a b dst raw slot dstRoom (by omega), ite_eq_left active]
    exact finished_raw_value a b raw slot (by omega) active
  · rw [ite_eq_right active, coeff_product_outside a b slot (by omega)]

/-- With adequate buffers, the normalized active destination is the exact
GF64 polynomial product. Empty inputs return the empty active prefix. -/
def ActualDenseMulPolynomialProduct : Prop :=
  ∀ {K : Type} (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64),
    RawMulAgrees kernels → reduceAgrees kernels →
    ∀ (a b dst : Slice U64) (raw : Slice Raw),
      (a.length = 0 ∨ b.length = 0) ∨
        (a.length + b.length ≤ dst.length ∧ a.length + b.length ≤ raw.length) →
      ∃ normalized output scratch,
        bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.mul_into dictionary kernels a b dst raw =
          Result.ok (normalized, output, scratch) ∧
        slicePolynomial (prefixSlice output normalized.val) = slicePolynomial a * slicePolynomial b

theorem mul_into_polynomial_refines :
    ActualDenseMulPolynomialProduct := by
  intro K kernels rawMul reduce a b dst raw valid
  have normal := mul_into_refines kernels rawMul reduce a b dst raw
  by_cases empty : a.length = 0 ∨ b.length = 0
  · rw [ite_eq_left empty] at normal
    refine ⟨0#usize, dst, raw, normal, ?_⟩
    rcases empty with left | right
    · simp [slicePolynomial, prefixSlice, left]
    · simp [slicePolynomial, prefixSlice, right]
  · have room := valid.resolve_left empty
    have sizeBound := room.1.trans (show dst.length ≤ Usize.max from dst.length_ineq)
    rw [ite_eq_right empty, ite_eq_left sizeBound, ite_eq_left room] at normal
    obtain ⟨normalized, execution, length⟩ := normal
    refine ⟨normalized, _, _, execution, ?_⟩
    have prefixBound : a.length + b.length - 1 ≤ (finishedDst a b dst raw).length := by
      simp only [finished_dst_length]
      omega
    rw [length, normalized_prefix_polynomial _ _ prefixBound]
    exact finished_dst_product a b dst raw room.1 room.2

end BulksketchBridge.DenseMul
