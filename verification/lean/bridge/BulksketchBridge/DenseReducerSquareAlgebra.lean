import BulksketchBridge.DenseReducerSquare
import BulksketchBridge.DenseRawSquareMeaning
import BulksketchBridge.RootTraceLoopSpec
import BulksketchBridge.ClosedLeafAdvance

namespace BulksketchBridge.DenseReducerSquare

open Aeneas.Std Algebra.Gf64 Polynomial
open DenseReducerAlgebra DenseCoefficient DenseNormalization RebuiltLfsr SliceKernels
open DenseMulConvolutionSpec MutableZip
open bulksketch.backend.contract
open scoped BulksketchBridge.DenseMulReductionSpec

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

/-- The backend preserves both borrowed slice widths. A successful
accelerated result has the same monic remainder as the scalar path.
The declined path leaves the final value to the original fallback. -/
def BackendSquareLaw {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (modulus table : Slice U64) (degree : Nat) : Prop :=
  ∀ (input dst : Slice U64) (raw : Slice Raw),
    input.length ≤ degree → dst.length = degree → 2 * degree < raw.length →
    ∃ accelerated active scratch,
      kernels.square_mod input table dst raw = .ok (accelerated, active, scratch) ∧
      active.length = degree ∧ scratch.length = raw.length ∧
      (accelerated = true →
        slicePolynomial active = (slicePolynomial input ^ 2) %ₘ slicePolynomial modulus)

private theorem update_agrees (table : Slice U64) (degree index : Nat) (coefficient : U64) (raw : Slice Raw) :
    DenseRawSquareMeaning.update table degree index coefficient raw =
      accumulateCoefficient table degree index coefficient raw := by
  simp only [DenseRawSquareMeaning.update, accumulateCoefficient, firstHigh, tableRow, Nat.add_mul, Nat.one_mul]

private theorem scan_agrees (input table : Slice U64) (degree index count : Nat) (raw : Slice Raw) :
    DenseRawSquareMeaning.accumulate input table degree raw index count =
      accumulateSquare input table degree raw index count := by
  induction count generalizing index raw with
  | zero => rfl
  | succ n ih =>
    simp only [DenseRawSquareMeaning.accumulate, accumulateSquare, update_agrees, ih]

private theorem output_length_value (output : Slice U64) (degree : Nat) (room : degree ≤ output.length) :
    (outputLength output degree).val = normalizedLength (output.val.take degree) ∧
      (outputLength output degree).val ≤ degree := by
  have listLen : (output.val.take degree).length = degree := by
    rw [List.length_take, Nat.min_eq_left room]
  have bounded : normalizedLength (output.val.take degree) ≤ degree := by
    simpa only [listLen] using normalizedLength_le (output.val.take degree)
  have max : output.length ≤ Usize.max := output.length_ineq
  have wordValue : (outputLength output degree).val = normalizedLength (output.val.take degree) := by
    simp only [outputLength, prefixSlice, Slice.from_val]
    exact ClosedLeafAdvance.word_val _ (by omega)
  exact ⟨wordValue, wordValue ▸ bounded⟩

private theorem restored_prefix (dst replacement : Slice U64) (degree : Nat)
    (width : replacement.length = degree) (room : degree ≤ dst.length) :
    prefixSlice (restorePrefix dst replacement) degree = replacement := by
  apply Slice.ext
  have replacementRoom : replacement.val.length ≤ dst.val.length := by
    change replacement.length ≤ dst.length
    omega
  have wordCount : replacement.val.length = degree := width
  simp only [prefixSlice, restorePrefix, Slice.from_val, List.setSlice!, Nat.sub_zero, Nat.zero_add,
    List.take_zero, List.nil_append, Nat.min_eq_left replacementRoom, List.take_length]
  rw [← wordCount, List.take_left]

/-- The actual Dense square provides the modular square callback used
in the original trace loop. Both source dispatch paths satisfy it. -/
def ActualNativeModularSquare : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    ∀ (modulus table : Slice U64) (degree : Nat),
      4 ≤ modulus.length → modulus.length = degree + 1 → modulus[degree]! = 1#u64 →
      table.length = degree * (degree / 2) → CorrectTable modulus table degree →
      BackendSquareLaw kernels modulus table degree →
      RootTrace.ModularSquareLaw bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into
        kernels modulus table degree

theorem native_modular_square : ActualNativeModularSquare := by
  intro K kernels rawLaw squareLaw reduceLaw modulus table degree minimum shape monic tableLen tableCorrect
    backend input dst raw inputRoom dstRoom rawRoom
  have originalDegree : modulus.length - 1 = degree := by omega
  have dstWidth : (prefixSlice dst degree).length = degree :=
    (prefix_length _ _).trans (Nat.min_eq_left dstRoom)
  obtain ⟨accelerated, active, scratch, called, activeLen, scratchLen, correct⟩ :=
    backend input (prefixSlice dst degree) raw inputRoom dstWidth rawRoom
  have modeled := square_mod_into_refines kernels rawLaw squareLaw reduceLaw input modulus table dst raw
    minimum (by rw [originalDegree]; exact monic) (by rw [originalDegree]; exact inputRoom)
    (by rw [originalDegree]; exact dstRoom) (by rw [originalDegree]; exact rawRoom)
    (by rw [originalDegree]; exact tableLen)
    accelerated active scratch (by rw [originalDegree]; exact called)
    (fun _ => by rw [originalDegree, scratchLen]; omega)
  rw [originalDegree] at modeled
  let dst1 := restorePrefix dst active
  have dst1Len : dst1.length = dst.length := restore_length _ _
  cases accelerated
  · let initialized := zeroRaw scratch degree
    let acc := accumulateSquare input table degree initialized 0 input.length
    let reduced := mapFrom (prefixSlice dst1 degree) acc (fun _ word => DenseMulReductionSpec.reduceWord word) 0
    let output := restorePrefix dst1 reduced
    have initLen : initialized.length = degree := by
      have enough : degree ≤ scratch.length := by omega
      simp only [initialized, zeroRaw, Slice.length, Slice.from_val, List.length_replicate,
        Nat.min_eq_left enough]
    have initZero : ∀ i < degree, initialized[i]! = ⟨0#u64, 0#u64⟩ := by
      intro i activeIndex
      have enough : degree ≤ scratch.length := by omega
      simp only [initialized, zeroRaw, Slice.getElem!_Nat_eq, Slice.from_val, Nat.min_eq_left enough,
        List.getElem!_replicate, activeIndex]
      rfl
    obtain ⟨outLen, represented⟩ := DenseRawSquareMeaning.reduced_destination input modulus table dst1 degree initialized
      shape monic inputRoom tableCorrect initLen (by omega) initZero
    rw [scan_agrees] at outLen represented
    change output.length = dst1.length at outLen
    change slicePolynomial (prefixSlice output (normalizedLength (output.val.take degree))) = _ at represented
    have ⟨lengthValue, lengthBound⟩ := output_length_value output degree (by omega)
    refine ⟨outputLength output degree, output, scratch.setSlice! 0 acc.val, modeled, lengthBound,
      outLen.trans dst1Len, by rw [Slice.setSlice!_length, scratchLen], ?_⟩
    rw [lengthValue, represented]
  · have ⟨lengthValue, lengthBound⟩ := output_length_value dst1 degree (by omega)
    refine ⟨outputLength dst1 degree, dst1, scratch, modeled, lengthBound, dst1Len, scratchLen, ?_⟩
    rw [lengthValue, normalized_prefix_polynomial dst1 degree (by omega),
      restored_prefix dst active degree activeLen dstRoom]
    exact correct rfl

end BulksketchBridge.DenseReducerSquare
