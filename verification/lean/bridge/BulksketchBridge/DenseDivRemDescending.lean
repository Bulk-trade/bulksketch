import Arithmetic.DenseDivRemGenerated
import BulksketchBridge.DenseDivRemControl

namespace BulksketchBridge.DenseDivRem

open Aeneas Aeneas.Std BulksketchBridge DenseDivision
open bulksketch.backend.contract
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial
open scoped BulksketchBridge.DenseMulReductionSpec

set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

abbrev dictionary := DenseMulReductionSpec.dictionary

theorem descending_step {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (mul : MulWordLaw kernels) (reduce : DenseMul.reduceAgrees kernels)
    (rawMultiply : DenseMulConvolutionSpec.RawMulAgrees kernels)
    (b q : Slice U64) (raw : Slice Raw) (inverse : U64)
    (degree stop top : Usize) (offset : Nat)
    (cursor : stop.val = top.val + 1) (offsetValue : top.val = degree.val + offset)
    (qRoom : offset < q.length) (rawRoom : top.val < raw.length) (divisorRoom : degree.val ≤ b.length) :
    let factor := factorWord inverse raw[top.val]!
    div_rem_into_loop1.body dictionary kernels b inverse degree (reverseRange degree stop) q raw =
      .ok (.cont (reverseRange degree top, q.setAtNat offset factor, updateRaw b factor offset top.val raw)) := by
  have next := reverse_next degree stop top (by omega) cursor
  obtain ⟨slot, old, offsetOk, slotExact, writeOk⟩ :=
    quotient_write q degree top offset offsetValue qRoom
  let factor := factorWord inverse raw[top.val]!
  let finish (state : Slice Raw) : ControlFlow (ReverseRange × Slice U64 × Slice Raw) (Slice U64 × Slice Raw) :=
    .cont (reverseRange degree top, q.setAtNat offset factor, state)
  have ordered : slot.val ≤ top.val := by omega
  have width : top.val - slot.val = degree.val := by omega
  change _ = Result.ok (finish (updateRaw b factor offset top.val raw))
  simp only [div_rem_into_loop1.body, next, bind_ok]
  dsimp! only
  simp only [read_normal raw top rawRoom, reduce_normal kernels reduce, bind_ok]
  by_cases inverseOne : inverse = 1#u64
  · have factorEq : DenseMulReductionSpec.reduceWord raw[top.val]! = factor := by simp only [factor, factorWord, inverseOne, ite_true]
    simp only [inverseOne, bne_self_eq_false, Bool.false_eq_true, ite_false, factorEq, offsetOk, writeOk, bind_ok]
    dsimp! only
    by_cases factorZero : factor = 0#u64
    · simp only [factorZero, ite_true, update_zero, finish]
    · simp only [factorZero, ite_false]
      by_cases factorOne : factor = 1#u64
      · simp only [factorOne, ite_true]
        have wrote := unit_row_call div_rem_into_loop1_loop2 (by
          intro left right same
          obtain ⟨back, ran, write⟩ := unit_loop_other left right same 0 (Nat.zero_le _) (fun z => z)
          exact ⟨back, ran, write left.length⟩) raw b slot top degree ordered (by omega) width divisorRoom finish
        simpa only [rowCall, slotExact, finish, factorOne] using wrote
      · simp only [factorOne, ite_false]
        let run := fun iter back => div_rem_into_loop1_loop3 dictionary kernels iter back factor
        have wrote := product_row_call run factor (by
          intro left right same
          obtain ⟨back, ran, write⟩ := product_loop_other kernels rawMultiply factor left right same 0 (Nat.zero_le _) (fun z => z)
          exact ⟨back, ran, write left.length⟩) raw b slot top degree ordered (by omega) width divisorRoom factorZero factorOne finish
        simpa only [run, rowCall, slotExact, finish] using wrote
  · have branch : (inverse != 1#u64) = true := by simp [inverseOne]
    have factorNormal : kernels.ArithmeticInst.mul (DenseMulReductionSpec.reduceWord raw[top.val]!) inverse = .ok factor := by
      simpa only [factor, factorWord, inverseOne, ite_false] using mul (DenseMulReductionSpec.reduceWord raw[top.val]!) inverse
    simp only [branch, ite_true, factorNormal, offsetOk, writeOk, bind_ok]
    dsimp! only
    by_cases factorZero : factor = 0#u64
    · simp only [factorZero, ite_true, update_zero, finish]
    · simp only [factorZero, ite_false]
      by_cases factorOne : factor = 1#u64
      · simp only [factorOne, ite_true]
        have wrote := unit_row_call div_rem_into_loop1_loop0 (by
          intro left right same
          obtain ⟨back, ran, write⟩ := unit_loop left right same 0 (Nat.zero_le _) (fun z => z)
          exact ⟨back, ran, write left.length⟩) raw b slot top degree ordered (by omega) width divisorRoom finish
        simpa only [rowCall, slotExact, finish, factorOne] using wrote
      · simp only [factorOne, ite_false]
        let run := fun iter back => div_rem_into_loop1_loop1 dictionary kernels iter back factor
        have wrote := product_row_call run factor (by
          intro left right same
          obtain ⟨back, ran, write⟩ := product_loop kernels rawMultiply factor left right same 0 (Nat.zero_le _) (fun z => z)
          exact ⟨back, ran, write left.length⟩) raw b slot top degree ordered (by omega) width divisorRoom factorZero factorOne finish
        simpa only [run, rowCall, slotExact, finish] using wrote

theorem descending_done {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (b q : Slice U64) (raw : Slice Raw) (inverse : U64) (degree stop : Usize)
    (exhausted : stop.val ≤ degree.val) :
    div_rem_into_loop1 dictionary kernels (reverseRange degree stop) b q raw inverse degree = .ok (q, raw) := by
  have none := reverse_done degree stop exhausted
  have body : div_rem_into_loop1.body dictionary kernels b inverse degree (reverseRange degree stop) q raw =
      .ok (.done (q, raw)) := by
    simp only [div_rem_into_loop1.body, none, bind_ok]
    rfl
  unfold div_rem_into_loop1 loop
  dsimp only
  simp only [body, bind_ok]

/-- The generated direct descending loop over all admitted quotient offsets. -/
theorem descending_loop {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (mul : MulWordLaw kernels) (reduce : DenseMul.reduceAgrees kernels)
    (rawMultiply : DenseMulConvolutionSpec.RawMulAgrees kernels)
    (b q : Slice U64) (raw : Slice Raw) (inverse : U64) (degree stop : Usize) (count : Nat)
    (cursor : stop.val = degree.val + count) (qRoom : count ≤ q.length)
    (rawRoom : stop.val ≤ raw.length) (divisorRoom : degree.val ≤ b.length) :
    div_rem_into_loop1 dictionary kernels (reverseRange degree stop) b q raw inverse degree =
      .ok (descend b degree.val inverse count q raw) := by
  induction count generalizing stop q raw with
  | zero =>
    exact descending_done kernels b q raw inverse degree stop (by omega)
  | succ count ih =>
    have stopMax : stop.val ≤ Usize.max := by scalar_tac
    let top := ClosedLeafAdvance.usizeWord (degree.val + count)
    have topVal : top.val = degree.val + count := ClosedLeafAdvance.word_val _ (by omega)
    have body := descending_step kernels mul reduce rawMultiply b q raw inverse degree stop top count
      (by omega) topVal (by omega) (by omega) divisorRoom
    conv_lhs => unfold div_rem_into_loop1 loop
    dsimp only
    rw [body, bind_ok]
    let factor := factorWord inverse raw[top.val]!
    let nextQ := q.setAtNat count factor
    let nextRaw := updateRaw b factor count top.val raw
    change div_rem_into_loop1 dictionary kernels (reverseRange degree top) b nextQ nextRaw inverse degree = _
    rw [ih nextQ nextRaw top topVal (by unfold nextQ; rw [Slice.setAtNat_length]; omega)
      (by unfold nextRaw; rw [update_raw_length]; omega)]
    simp only [descend, nextQ, nextRaw, factor, topVal]

end BulksketchBridge.DenseDivRem
