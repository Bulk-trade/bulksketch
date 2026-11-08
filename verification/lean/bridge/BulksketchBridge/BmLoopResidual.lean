import BulksketchBridge.BmLoopResidualSpec
import BulksketchBridge.BmLoop
import BulksketchBridge.BmCurrentDiscrepancy

namespace BulksketchBridge.BmLoop

open Aeneas.Std BmDiscrepancy BmEvenStep BmStepControl
open bulksketch.backend.contract bulksketch.types
open Algebra.Gf64

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

theorem algebraic_step {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (raw : RawArithmetic kernels) (reduce : ReduceArithmetic kernels)
    (input : Input) (state next : State) (difference initial : Slice U64) (processed : Nat)
    (reconstructed : Reconstruction.Prefix difference initial input.syndromes processed)
    (processedBound : state.1.«end».val < processed) (admitted : Admitted input state)
    (algebra : Algebraic input state) (taken : step input state = .cont next) : Algebraic input next := by
  rcases state with ⟨iter, meter, connection, previous, saved, degree, previousLen, shift, scale⟩
  change iter.«end».val < processed at processedBound
  obtain ⟨budgetEnd, syndromeRoom, connectionRoom, previousRoom, savedRoom, scalar⟩ := admitted
  have degreeBudget := scalar.degreeBudget
  have degreeIndex := scalar.degreeIndex
  by_cases exhausted : iter.«end».val ≤ iter.start.val
  · simp only [step, exhausted, ite_true] at taken
    cases taken
  have active : iter.start.val < iter.«end».val := by omega
  have lenMax : input.syndromes.length ≤ Usize.max := input.syndromes.length_ineq
  have cursor := scalar.cursor
  have prevPositive := scalar.previousPositive
  have indexVal := increment_val iter.start (by omega)
  have shiftVal := increment_val shift (by omega)
  have lenVal := increment_val degree (by omega)
  have prelude : PreludeBounds connection input.syndromes degree iter.start :=
    ⟨by omega, by omega, by omega⟩
  cases charged : stepCharge iter.start meter input.cost with
  | mk payment finalMeter =>
    cases payment with
    | Err error =>
      simp only [step, exhausted, ite_false, charged] at taken
      cases taken
    | Ok paidUnit =>
      cases paidUnit
      by_cases even : iter.start.val % 2 = 0
      · have current := BmCurrentDiscrepancy.current_discrepancy kernels raw reduce connection
          input.syndromes degree iter.start prelude degreeIndex
        by_cases zero : deltaWord connection input.syndromes degree iter.start = 0#u64
        · simp only [step, exhausted, ite_false, charged, even, ite_true, zero] at taken
          injection taken with nextEq
          subst next
          rw [zero, show toField (0#u64 : U64).bv = 0 from toField_zero] at current
          simpa only [Algebraic, nextRange, indexVal, shiftVal] using BmResidualInvariant.advance algebra current
        · by_cases over : input.budget.val < nextDegree degree iter.start
          · simp only [step, exhausted, ite_false, charged, even, ite_true, zero, over] at taken
            cases taken
          · simp only [step, exhausted, ite_false, charged, even, ite_true, zero, over] at taken
            injection taken with nextEq
            subst next
            by_cases grows : 2 * degree.val ≤ iter.start.val
            · have within : iter.start.val + 1 - degree.val ≤ input.budget.val := by
                simpa only [nextDegree, grows, ite_true] using
                  (show nextDegree degree iter.start ≤ input.budget.val by omega)
              have candidateVal := ClosedLeafAdvance.word_val (iter.start.val + 1 - degree.val) (by omega)
              simp only [BmAccepted.expectedAccepted, grows, ite_true, Algebraic, nextRange, indexVal,
                nextDegree, lenVal, candidateVal, show (1#usize).val = 1 by simp]
              exact BmResidualInvariant.accepted_grow algebra scalar connectionRoom previousRoom even grows
                (deltaWord connection input.syndromes degree iter.start) zero within current
            · have candidateVal := ClosedLeafAdvance.word_val degree.val (by omega)
              simp only [BmAccepted.expectedAccepted, grows, ite_false, Algebraic, nextRange, indexVal,
                nextDegree, lenVal, candidateVal, shiftVal]
              exact BmResidualInvariant.accepted_stay algebra scalar connectionRoom previousRoom even grows
                (deltaWord connection input.syndromes degree iter.start) current
      · have odd : iter.start.val % 2 = 1 := by omega
        simp only [step, exhausted, ite_false, charged, even, eq_self, ite_true] at taken
        injection taken with nextEq
        subst next
        simpa only [Algebraic, nextRange, indexVal, shiftVal] using
          BmResidualInvariant.odd_advance algebra odd degreeIndex prelude.syndromes
            (by omega) reconstructed

private theorem success_exhausted (input : Input) (state : State) (reply : BmTerminal.Return)
    (taken : step input state = .done reply) (degree : Usize) (successful : reply.1 = .Ok (.Ok degree)) :
    state.1.«end».val ≤ state.1.start.val := by
  rcases state with ⟨iter, meter, connection, previous, saved, d, previousLen, shift, scale⟩
  change iter.«end».val ≤ iter.start.val
  by_contra notExhausted
  cases paid : stepCharge iter.start meter input.cost with
  | mk payment finalMeter =>
    cases payment with
    | Err error =>
      simp only [step, notExhausted, ite_false, paid] at taken
      injection taken with exactReply
      subst reply
      cases successful
    | Ok paidUnit =>
      cases paidUnit
      by_cases even : iter.start.val % 2 = 0
      · by_cases zero : deltaWord connection input.syndromes d iter.start = 0#u64
        · simp only [step, notExhausted, ite_false, paid, even, ite_true, zero] at taken
          cases taken
        · by_cases over : input.budget.val < nextDegree d iter.start
          · simp only [step, notExhausted, ite_false, paid, even, ite_true, zero, over] at taken
            injection taken with exactReply
            subst reply
            cases successful
          · simp only [step, notExhausted, ite_false, paid, even, ite_true, zero, over] at taken
            cases taken
      · simp only [step, notExhausted, ite_false, paid, even, eq_self, ite_true] at taken
        cases taken

private theorem run_final_invariant {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (raw : RawArithmetic kernels) (reduce : ReduceArithmetic kernels)
    (input : Input) (state last : State) (reply : BmTerminal.Return) (fuel : Nat)
    (difference initial : Slice U64) (processed : Nat)
    (reconstructed : Reconstruction.Prefix difference initial input.syndromes processed)
    (ordered : state.1.start.val ≤ state.1.«end».val) (processedBound : state.1.«end».val < processed)
    (admitted : Admitted input state) (algebra : Algebraic input state)
    (returned : run input fuel state = some (last, reply)) :
    Admitted input last ∧ Algebraic input last ∧ last.1.«end» = state.1.«end» ∧
      last.1.start.val ≤ last.1.«end».val ∧ step input last = .done reply := by
  induction fuel generalizing state with
  | zero =>
    cases taken : step input state with
    | done result =>
      rw [run, taken] at returned
      cases returned
      exact ⟨admitted, algebra, rfl, ordered, taken⟩
    | cont next =>
      rw [run, taken] at returned
      cases returned
  | succ fuel ih =>
    cases taken : step input state with
    | done result =>
      rw [run, taken] at returned
      cases returned
      exact ⟨admitted, algebra, rfl, ordered, taken⟩
    | cont next =>
      rw [run, taken] at returned
      obtain ⟨valid, index, sameEnd⟩ := advances input state next admitted taken
      have nextOrdered : next.1.start.val ≤ next.1.«end».val := by
        have fits : state.1.start.val + 1 ≤ state.1.«end».val := by
          by_contra notFit
          rcases state with ⟨iter, meter, connection, previous, saved, degree, previousLen, shift, scale⟩
          change ¬ iter.start.val + 1 ≤ iter.«end».val at notFit
          simp only [step, show iter.«end».val ≤ iter.start.val by omega, ite_true] at taken
          cases taken
        rw [index, sameEnd]
        exact fits
      have alg := algebraic_step kernels raw reduce input state next difference initial processed
        reconstructed processedBound admitted algebra taken
      obtain ⟨finalValid, finalAlg, endEq, finalOrdered, lastStep⟩ :=
        ih next nextOrdered (by simpa only [sameEnd] using processedBound) valid alg returned
      exact ⟨finalValid, finalAlg, endEq.trans sameEnd, finalOrdered, lastStep⟩

theorem loop_residual_refines : ActualBmLoopResidual := by
  intro K kernels raw reduce mul inverse input state difference initial processed reconstructed
    ordered processedBound admitted algebra
  obtain ⟨last, reply, modeled, native⟩ := run_refines kernels raw reduce mul inverse input state _ admitted rfl
  obtain ⟨valid, alg, endEq, lastOrdered, lastStep⟩ := run_final_invariant kernels raw reduce input
    state last reply _ difference initial processed reconstructed ordered processedBound admitted algebra modeled
  refine ⟨last, reply, modeled, native, valid, alg, endEq, lastOrdered, lastStep, ?_⟩
  intro degree successful
  rw [← endEq]
  exact Nat.le_antisymm lastOrdered (success_exhausted input last reply lastStep degree successful)

end BulksketchBridge.BmLoop
