import BulksketchBridge.BmLocatorResidual

namespace BulksketchBridge.BmLoop

open Aeneas.Std BmTerminal BmStepControl
open bulksketch.types

def widths : State → Nat × Nat × Nat
  | (_, _, connection, previous, saved, _, _, _, _) =>
    (connection.length, previous.length, saved.length)

private theorem accepted_widths (next : IndexRange) (meter : WorkMeter)
    (connection previous saved : Slice U64) (degree candidate len previousLen shift : Usize)
    (scale delta : U64) (grows : Prop) [Decidable grows] :
    widths (BmAccepted.expectedAccepted next meter connection previous saved degree candidate len
      previousLen shift scale delta grows) = (connection.length, previous.length, saved.length) := by
  unfold BmAccepted.expectedAccepted
  split <;> simp only [widths, BmConnectionUpdate.expectedConnection, BmConnectionUpdate.clearedConnection,
    BmConnectionUpdate.scaledConnection, Slice.setSlice!_length]

theorem step_widths (input : Input) (state next : State) (taken : step input state = .cont next) :
    widths next = widths state := by
  rcases state with ⟨iter, meter, connection, previous, saved, degree, previousLen, shift, scale⟩
  by_cases exhausted : iter.«end».val ≤ iter.start.val
  · simp only [step, exhausted, ite_true] at taken
    cases taken
  cases charged : stepCharge iter.start meter input.cost with
  | mk payment finalMeter =>
    cases payment with
    | Err error =>
      simp only [step, exhausted, ite_false, charged] at taken
      cases taken
    | Ok paidUnit =>
      cases paidUnit
      simp only [step, exhausted, ite_false, charged] at taken
      let delta := if iter.start.val % 2 = 0 then
        BmEvenStep.deltaWord connection input.syndromes degree iter.start else 0#u64
      change (if delta = 0#u64 then ControlFlow.cont (nextRange iter, finalMeter, connection, previous, saved,
          degree, previousLen, incremented shift, scale)
        else if input.budget.val < BmEvenStep.nextDegree degree iter.start then
          ControlFlow.done (finish input connection previous saved finalMeter (.Ok (.Err .DegreeExceedsBudget)))
        else ControlFlow.cont (BmAccepted.expectedAccepted (nextRange iter) finalMeter connection previous saved
          degree (ClosedLeafAdvance.usizeWord (BmEvenStep.nextDegree degree iter.start)) (incremented degree)
          previousLen shift scale delta (2 * degree.val ≤ iter.start.val))) = .cont next at taken
      split at taken
      · injection taken with same
        subst next
        rfl
      · split at taken
        · cases taken
        · injection taken with same
          subst next
          exact accepted_widths _ _ _ _ _ _ _ _ _ _ _ _ _

theorem run_widths (input : Input) (fuel : Nat) (state last : State) (reply : Return)
    (returned : run input fuel state = some (last, reply)) : widths last = widths state := by
  induction fuel generalizing state with
  | zero =>
    cases taken : step input state <;> rw [run, taken] at returned
    · cases returned
    · cases returned
      rfl
  | succ fuel ih =>
    cases taken : step input state with
    | done result =>
      rw [run, taken] at returned
      cases returned
      rfl
    | cont next =>
      rw [run, taken] at returned
      exact (ih next returned).trans (step_widths input state next taken)

end BulksketchBridge.BmLoop
