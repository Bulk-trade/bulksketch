import BulksketchBridge.BmLoopSpec
import BulksketchBridge.BmAccepted
import BulksketchBridge.BmEvenStep
import BulksketchBridge.BmScalar
import BulksketchBridge.BmTerminal
import BulksketchBridge.ClosedLeafAdvance

namespace BulksketchBridge.BmLoop

open Aeneas Aeneas.Std BmDiscrepancy BmEvenStep BmStepControl
open bulksketch.backend.contract bulksketch.decode.bm bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

abbrev nativeBody {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (input : Input) (state : State) : BmAccepted.BodyResult :=
  let (iter, meter, connection, previous, saved, degree, previousLen, shift, previousDelta) := state
  locator_loop0.body fieldDictionary kernels input.restoreConnection input.restorePrevious input.tail
    input.restoreSaved input.syndromes input.budget input.cost iter meter
    connection previous saved degree previousLen shift previousDelta

abbrev nativeLoop {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (input : Input) (state : State) : Result BmTerminal.Return :=
  let (iter, meter, connection, previous, saved, degree, previousLen, shift, previousDelta) := state
  locator_loop0 fieldDictionary kernels input.restoreConnection input.restorePrevious input.tail
    input.restoreSaved iter input.syndromes input.budget meter input.cost
    connection previous saved degree previousLen shift previousDelta

theorem increment_val (word : Usize) (fits : word.val + 1 ≤ Usize.max) :
    (incremented word).val = word.val + 1 :=
  ClosedLeafAdvance.word_val _ fits

theorem update_bounds (connection previous saved : Slice U64) (budget degree index shift previousLen : Usize)
    (connectionRoom : budget.val < connection.length) (previousRoom : budget.val < previous.length)
    (savedRoom : budget.val < saved.length)
    (scalar : BmScalar.Invariant index.val budget.val degree.val previousLen.val shift.val)
    (within : nextDegree degree index ≤ budget.val) (shiftFits : shift.val + 1 ≤ Usize.max) :
    BmAccepted.UpdateBounds connection previous saved degree index shift previousLen := by
  obtain ⟨_, shifted, _⟩ := BmScalar.shifted_window_bounds index.val budget.val degree.val previousLen.val
    shift.val scalar within
  change shift.val + previousLen.val ≤ nextDegree degree index + 1 at shifted
  have prevBudget := scalar.previousBudget
  have degreeBudget := scalar.degreeBudget
  exact ⟨by omega, by omega, by omega, fun _ => ⟨by omega, by omega⟩, fun _ => shiftFits⟩

/-- All original outer branches have the same exact result as the finite
step, including uncharged index zero, work exhaustion and final reversal. -/
theorem body_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (raw : RawArithmetic kernels) (reduce : ReduceArithmetic kernels) (mul : BmMutable.NativeMul kernels)
    (inverse : BmTerminal.NativeInverse kernels) (input : Input) (state : State)
    (admitted : Admitted input state) :
    nativeBody kernels input state = .ok (step input state) := by
  rcases state with ⟨iter, meter, connection, previous, saved, degree, previousLen, shift, previousDelta⟩
  obtain ⟨budgetEnd, syndromeRoom, connectionRoom, previousRoom, savedRoom, scalar⟩ := admitted
  have degreeBudget := scalar.degreeBudget
  have degreeIndex := scalar.degreeIndex
  by_cases exhausted : iter.«end».val ≤ iter.start.val
  · simpa only [step, exhausted, ite_true] using BmTerminal.body_refines kernels mul inverse
      input.restoreConnection input.restorePrevious input.restoreSaved input.tail input.syndromes input.budget
      input.cost iter meter connection previous saved degree previousLen shift previousDelta exhausted (by omega)
  have active : iter.start.val < iter.«end».val := by omega
  have lenMax : input.syndromes.length ≤ Usize.max := input.syndromes.length_ineq
  have cursor := scalar.cursor
  have prevPositive := scalar.previousPositive
  have shiftFits : shift.val + 1 ≤ Usize.max := by omega
  have twiceFits : 2 * degree.val ≤ Usize.max := by omega
  have prelude : PreludeBounds connection input.syndromes degree iter.start :=
    ⟨by omega, by omega, by omega⟩
  cases charged : stepCharge iter.start meter input.cost with
  | mk reply finalMeter =>
    cases reply with
    | Err error =>
      simpa only [step, exhausted, ite_false, charged, finish] using
        charge_failure_refines BmDiscrepancy.fieldDictionary kernels input.restoreConnection input.restorePrevious
          input.restoreSaved input.tail input.syndromes input.budget input.cost iter meter finalMeter
          connection previous saved degree previousLen shift previousDelta error active charged
    | Ok paidUnit =>
      cases paidUnit
      by_cases even : iter.start.val % 2 = 0
      · by_cases zero : deltaWord connection input.syndromes degree iter.start = 0#u64
        · simpa only [step, exhausted, ite_false, charged, even, ite_true, zero] using
            even_zero_refines kernels raw reduce input.restoreConnection input.restorePrevious input.restoreSaved
              input.tail input.syndromes input.budget input.cost iter meter finalMeter connection previous saved
              degree previousLen shift previousDelta active even prelude charged zero shiftFits
        · by_cases over : input.budget.val < nextDegree degree iter.start
          · simpa only [step, exhausted, ite_false, charged, even, ite_true, zero, over, finish] using
              degree_exceeds_refines kernels raw reduce input.restoreConnection input.restorePrevious
                input.restoreSaved input.tail input.syndromes input.budget input.cost iter meter finalMeter
                connection previous saved degree previousLen shift previousDelta active even prelude charged zero twiceFits over
          · have within : nextDegree degree iter.start ≤ input.budget.val := by omega
            have bounds := update_bounds connection previous saved input.budget degree iter.start shift previousLen
              connectionRoom previousRoom savedRoom scalar within shiftFits
            obtain ⟨candidate, len, candidateVal, lenVal, updated⟩ := BmAccepted.accepted_update_refines
              kernels raw reduce mul input.restoreConnection input.restorePrevious input.restoreSaved input.tail
              input.syndromes input.budget input.cost iter meter finalMeter connection previous saved
              degree previousLen shift previousDelta active even prelude charged zero twiceFits within bounds
            have candidateEq : candidate = ClosedLeafAdvance.usizeWord (nextDegree degree iter.start) := by
              apply UScalar.eq_of_val_eq
              rw [candidateVal, ClosedLeafAdvance.word_val _ (by omega)]
            have lenEq : len = incremented degree := by
              apply UScalar.eq_of_val_eq
              rw [lenVal, increment_val degree (by omega)]
            simpa only [step, exhausted, ite_false, charged, even, ite_true, zero, over, candidateEq, lenEq] using updated
      · have odd : iter.start.val % 2 = 1 := by omega
        simpa only [step, exhausted, ite_false, charged, even, eq_self, ite_true] using
          odd_skip_refines BmDiscrepancy.fieldDictionary kernels input.restoreConnection input.restorePrevious
            input.restoreSaved input.tail input.syndromes input.budget input.cost iter meter finalMeter
            connection previous saved degree previousLen shift previousDelta active odd shiftFits charged

private theorem accepted_admitted (input : Input) (iter : IndexRange) (meter : WorkMeter)
    (connection previous saved : Slice U64) (degree previousLen shift : Usize) (previousDelta delta : U64)
    (admitted : Admitted input (iter, meter, connection, previous, saved, degree, previousLen, shift, previousDelta))
    (active : iter.start.val < iter.«end».val) (within : nextDegree degree iter.start ≤ input.budget.val)
    (finalMeter : WorkMeter) :
    Admitted input (BmAccepted.expectedAccepted (nextRange iter) finalMeter connection previous saved
      degree (ClosedLeafAdvance.usizeWord (nextDegree degree iter.start)) (incremented degree)
      previousLen shift previousDelta delta (2 * degree.val ≤ iter.start.val)) := by
  obtain ⟨budgetEnd, syndromeRoom, connectionRoom, previousRoom, savedRoom, scalar⟩ := admitted
  have lenMax : input.syndromes.length ≤ Usize.max := input.syndromes.length_ineq
  have cursor := scalar.cursor
  have prevPositive := scalar.previousPositive
  have degreeBudget := scalar.degreeBudget
  have shiftVal := increment_val shift (by omega)
  have degreeVal := increment_val degree (by omega)
  have indexVal := increment_val iter.start (by omega)
  have connectionLen (len candidate : Nat) : (BmConnectionUpdate.expectedConnection connection previous
      len candidate shift.val previousLen.val previousDelta delta).length = connection.length := by
    simp only [BmConnectionUpdate.expectedConnection, BmConnectionUpdate.clearedConnection,
      BmConnectionUpdate.scaledConnection, Slice.setSlice!_length]
  by_cases grows : 2 * degree.val ≤ iter.start.val
  · have admittedGrow : iter.start.val + 1 - degree.val ≤ input.budget.val := by
      simpa only [nextDegree, grows, ite_true] using within
    have candidateVal := ClosedLeafAdvance.word_val (iter.start.val + 1 - degree.val) (by omega)
    simp only [BmAccepted.expectedAccepted, grows, ite_true, Admitted, nextRange,
      connectionLen, Slice.setSlice!_length, indexVal, nextDegree, degreeVal, candidateVal]
    exact ⟨budgetEnd, syndromeRoom, connectionRoom, previousRoom, savedRoom,
      by simpa only [show (1#usize).val = 1 by simp] using BmScalar.grow _ _ _ _ _ scalar admittedGrow⟩
  · simp only [BmAccepted.expectedAccepted, grows, ite_false, Admitted, nextRange, connectionLen,
      indexVal, shiftVal]
    exact ⟨budgetEnd, syndromeRoom, connectionRoom, previousRoom, savedRoom, BmScalar.advance _ _ _ _ _ scalar⟩

/-- Every continuation preserves the exact row bounds and advances the
finite index once while retaining the original exclusive stop. -/
theorem advances (input : Input) (state next : State) (admitted : Admitted input state)
    (taken : step input state = .cont next) :
    Admitted input next ∧ next.1.start.val = state.1.start.val + 1 ∧ next.1.«end» = state.1.«end» := by
  rcases state with ⟨iter, meter, connection, previous, saved, degree, previousLen, shift, previousDelta⟩
  obtain ⟨budgetEnd, syndromeRoom, connectionRoom, previousRoom, savedRoom, scalar⟩ := admitted
  by_cases exhausted : iter.«end».val ≤ iter.start.val
  · simp only [step, exhausted, ite_true] at taken
    cases taken
  have active : iter.start.val < iter.«end».val := by omega
  have lenMax : input.syndromes.length ≤ Usize.max := input.syndromes.length_ineq
  have cursor := scalar.cursor
  have prevPositive := scalar.previousPositive
  have shiftVal := increment_val shift (by omega)
  have indexVal := increment_val iter.start (by omega)
  cases charged : stepCharge iter.start meter input.cost with
  | mk reply finalMeter =>
    cases reply with
    | Err error =>
      simp only [step, exhausted, ite_false, charged] at taken
      cases taken
    | Ok paidUnit =>
      cases paidUnit
      let delta := if iter.start.val % 2 = 0 then deltaWord connection input.syndromes degree iter.start else 0#u64
      simp only [step, exhausted, ite_false, charged] at taken
      change (if delta = 0#u64 then
        ControlFlow.cont (nextRange iter, finalMeter, connection, previous, saved, degree, previousLen,
          incremented shift, previousDelta)
        else if input.budget.val < nextDegree degree iter.start then
          ControlFlow.done (finish input connection previous saved finalMeter (.Ok (.Err .DegreeExceedsBudget)))
        else ControlFlow.cont (BmAccepted.expectedAccepted (nextRange iter) finalMeter connection previous saved degree
          (ClosedLeafAdvance.usizeWord (nextDegree degree iter.start)) (incremented degree) previousLen shift
          previousDelta delta (2 * degree.val ≤ iter.start.val))) = ControlFlow.cont next at taken
      by_cases zero : delta = 0#u64
      · rw [ite_eq_left zero] at taken
        injection taken with exactNext
        subst next
        exact ⟨⟨budgetEnd, syndromeRoom, connectionRoom, previousRoom, savedRoom,
          by simpa only [nextRange, indexVal, shiftVal] using BmScalar.advance _ _ _ _ _ scalar⟩, indexVal, rfl⟩
      · by_cases over : input.budget.val < nextDegree degree iter.start
        · simp only [zero, ite_false, over, ite_true] at taken
          cases taken
        · simp only [zero, ite_false, over] at taken
          injection taken with exactNext
          subst next
          refine ⟨accepted_admitted input iter meter connection previous saved degree previousLen shift
            previousDelta delta ⟨budgetEnd, syndromeRoom, connectionRoom, previousRoom, savedRoom, scalar⟩
              active (by omega) finalMeter, ?_⟩
          unfold BmAccepted.expectedAccepted
          split <;> exact ⟨indexVal, rfl⟩

private theorem loop_shape {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (input : Input) (state : State) :
    nativeLoop kernels input state = loop (nativeBody kernels input) state := by
  rcases state with ⟨_, _, _, _, _, _, _, _, _⟩
  rfl

theorem run_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (raw : RawArithmetic kernels) (reduce : ReduceArithmetic kernels) (mul : BmMutable.NativeMul kernels)
    (inverse : BmTerminal.NativeInverse kernels) (input : Input) (state : State) (fuel : Nat)
    (admitted : Admitted input state) (remaining : fuel = state.1.«end».val - state.1.start.val) :
    ∃ last result, run input fuel state = some (last, result) ∧ nativeLoop kernels input state = .ok result := by
  induction fuel generalizing state with
  | zero =>
    have exhausted : state.1.«end».val ≤ state.1.start.val := by omega
    rcases state with ⟨iter, meter, connection, previous, saved, degree, previousLen, shift, previousDelta⟩
    let state : State := (iter, meter, connection, previous, saved, degree, previousLen, shift, previousDelta)
    let result := BmTerminal.terminalResult input.restoreConnection input.restorePrevious input.restoreSaved
      input.tail connection previous saved degree meter
    have stopped : step input state = .done result := by
      change iter.«end».val ≤ iter.start.val at exhausted
      simp only [state, step, exhausted, ite_true, result]
    refine ⟨state, result, ?_, ?_⟩
    · change run input 0 state = some (state, result)
      rw [run, stopped]
    · change nativeLoop kernels input state = .ok result
      have evaluated := body_refines kernels raw reduce mul inverse input state admitted
      rw [stopped] at evaluated
      rw [loop_shape, loop, evaluated, bind_ok]
  | succ fuel ih =>
    have evaluated := body_refines kernels raw reduce mul inverse input state admitted
    cases taken : step input state with
    | done result =>
      refine ⟨state, result, ?_, ?_⟩
      · rw [run, taken]
      · rw [loop_shape, loop, evaluated, taken, bind_ok]
    | cont next =>
      obtain ⟨valid, index, stop⟩ := advances input state next admitted taken
      obtain ⟨last, result, reduced, native⟩ := ih next valid (by rw [stop, index]; omega)
      refine ⟨last, result, ?_, ?_⟩
      · rw [run, taken]
        exact reduced
      · rw [loop_shape, loop, evaluated, taken, bind_ok]
        exact (loop_shape kernels input next).symm.trans native

theorem loop_refines : ActualBmLoop := by
  intro K kernels raw reduce mul inverse input iter meter connection previous saved degree previousLen shift
    previousDelta state admitted
  exact run_refines kernels raw reduce mul inverse input state _ admitted rfl

end BulksketchBridge.BmLoop
