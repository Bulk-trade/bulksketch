import BulksketchBridge.DenseGcdSize
import BulksketchBridge.DenseDivRemComposition

namespace BulksketchBridge.DenseGcd

open Aeneas.Std DenseCoefficient BmEntry RebuiltLfsr
open bulksketch.backend.contract bulksketch.types
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial

set_option maxRecDepth 4096

private theorem run_raw_width (division : DivRem) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (law : DivisionLaw division kernels) (width fuel : Nat) (state final : State)
    (ready : Ready width state) (enough : state.rightLen.val ≤ fuel)
    (ran : run division kernels fuel state = .ok final) :
    final.raw.length = state.raw.length := by
  induction fuel generalizing state with
  | zero =>
    have stop : state.rightLen = 0#usize := UScalar.eq_of_val_eq (by change state.rightLen.val = 0; omega)
    simp only [run, stop, ite_true, Result.ok.injEq] at ran
    rw [← ran]
  | succ fuel ih =>
    by_cases stop : state.rightLen = 0#usize
    · simp only [run, stop, ite_true, Result.ok.injEq] at ran
      rw [← ran]
    · have positive : 0 < state.rightLen.val := by
        apply Nat.pos_of_ne_zero
        exact fun empty => stop (UScalar.eq_of_val_eq empty)
      obtain ⟨qLen, remLen, qOut, remOut, rawOut, call, qWidth, remWidth, rawWidth, smaller, normal⟩ :=
        law state.leftWords state.rightWords state.quotient state.remainder state.raw
          ready.leftNormal ready.rightNormal (ready.rightLength.symm ▸ positive)
          (by rw [ready.leftLength, ready.quotientWidth]; exact ready.leftRoom)
          (by rw [ready.leftLength, ready.remainderWidth]; exact ready.leftRoom)
          (by rw [ready.leftLength]; exact ready.leftRoom.trans_le ready.rawRoom)
      let next := state.advance ((qLen, remLen), qOut, remOut, rawOut)
      have admitted := ready.advance qLen remLen qOut remOut rawOut qWidth remWidth rawWidth smaller normal
      have normalNext : run division kernels fuel next = .ok final := by
        simpa only [run, stop, ite_false, call, bind_ok, next] using ran
      have nextFuel : next.rightLen.val ≤ fuel := by
        rw [ready.rightLength] at smaller
        change remLen.val ≤ fuel
        omega
      exact (ih next admitted nextFuel normalNext).trans rawWidth

private theorem destination_width (destinationSlice : Slice U64) (limit : Nat) (final : State) :
    (destination destinationSlice limit final).length = destinationSlice.length := by
  unfold destination
  split <;> simp only [restore_length]

private theorem work_width (work : Slice U64) (width : Nat) (final : State) :
    (restoreWork work width final).length = work.length := by
  unfold restoreWork
  rcases final.back final.left final.right final.remainder with ⟨left, right, spare⟩
  exact restore_length ..

/-- The original monic GCD call preserves the full native scratch widths,
    including the raw frame across all Euclidean rotations. -/
theorem native_gcd_widths (division : DivRem) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (law : DivisionLaw division kernels) (inverse : BmTerminal.NativeInverse kernels)
    (scale : TimesXMod.ExactScaleXor kernels)
    (a b dst work : Slice U64) (raw : Slice RawProduct) (aNormal : Normal a) (bNormal : Normal b)
    (dstRoom : max a.length b.length ≤ dst.length) (workRoom : 4 * (max a.length b.length + 1) ≤ work.length)
    (rawRoom : 2 * (max a.length b.length + 1) ≤ raw.length)
    (size : Usize) (out outWork : Slice U64) (outRaw : Slice RawProduct)
    (returned : monic_gcd_into division dictionary kernels a b dst work raw = .ok (size, out, outWork, outRaw)) :
    out.length = dst.length ∧ outWork.length = work.length ∧ outRaw.length = raw.length := by
  let limit := max a.length b.length
  let width := limit + 1
  let state := startState width a b work raw
  have aRoom : a.length < width := Nat.lt_succ_of_le (Nat.le_max_left _ _)
  have bRoom : b.length < width := Nat.lt_succ_of_le (Nat.le_max_right _ _)
  have rawFit : width ≤ raw.length := by change 2 * width ≤ raw.length at rawRoom; omega
  have ready := start_ready a b work raw width workRoom rawFit aRoom bRoom aNormal bNormal
  have fuel : state.rightLen.val ≤ b.length := by simp only [state, startState, Slice.len_val, Nat.le_refl]
  obtain ⟨final, modeled, _, _, _⟩ := run_refines division kernels law width b.length state ready fuel
  have finish : expected division kernels a b dst work raw =
      .ok (final.leftLen, destination dst limit final, restoreWork work width final, final.raw) := by
    simp only [expected, state, width, limit] at modeled ⊢
    rw [modeled, bind_ok]
  obtain ⟨frame, native, eqExpected⟩ := monic_gcd_refines division kernels a b dst work raw law inverse scale
    aNormal bNormal dstRoom workRoom rawRoom
  have same := Result.ok_injective ((returned.symm.trans native).trans (eqExpected.symm.trans finish))
  have outEq := congrArg (fun result : Output => result.2.1) same
  have workEq := congrArg (fun result : Output => result.2.2.1) same
  have rawEq := congrArg (fun result : Output => result.2.2.2) same
  dsimp only at outEq workEq rawEq
  rw [outEq, workEq, rawEq, destination_width, work_width]
  exact ⟨rfl, rfl, run_raw_width division kernels law width b.length state final ready fuel modeled⟩

#print axioms native_gcd_widths

end BulksketchBridge.DenseGcd
