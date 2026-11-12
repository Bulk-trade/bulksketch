import BulksketchBridge.BmAcceptedSpec
import BulksketchBridge.BmScalarSpec

namespace BulksketchBridge.BmLoop

open Aeneas.Std BmStepControl BmTerminal
open bulksketch.backend.contract bulksketch.decode.bm bulksketch.types

abbrev State := BmAccepted.Cont

structure Input where
  restoreConnection : Back
  restorePrevious : Back
  tail : Slice U64
  restoreSaved : Back
  syndromes : Slice U64
  budget : Usize
  cost : WorkUnits

/-- The range, active scratch prefixes and homogeneous cursor are admitted
through every iteration. Bounds at individual indexing operations follow. -/
def Admitted (input : Input) : State → Prop
  | (iter, _, connection, previous, saved, degree, previousLen, shift, _) =>
      2 * input.budget.val ≤ iter.«end».val ∧ iter.«end».val < input.syndromes.length ∧
      input.budget.val < connection.length ∧ input.budget.val < previous.length ∧
      input.budget.val < saved.length ∧
      BmScalar.Invariant iter.start.val input.budget.val degree.val previousLen.val shift.val

def finish (input : Input) (connection previous saved : Slice U64)
    (meter : WorkMeter) (reply : Reply) : Return :=
  (reply, joinBuffers input.restoreConnection input.restorePrevious input.restoreSaved
    input.tail connection previous saved, meter)

/-- Independent finite step, with the original cost and exact scratch frame.
The branch that increments without changing coefficients includes odd skips. -/
noncomputable def step (input : Input) : State → ControlFlow State Return
  | (iter, meter, connection, previous, saved, degree, previousLen, shift, previousDelta) =>
      if iter.«end».val ≤ iter.start.val then
        .done (terminalResult input.restoreConnection input.restorePrevious input.restoreSaved
          input.tail connection previous saved degree meter)
      else
        match stepCharge iter.start meter input.cost with
        | (.Err error, finalMeter) => .done (finish input connection previous saved finalMeter (.Err error))
        | (.Ok (), finalMeter) =>
          let delta := if iter.start.val % 2 = 0 then
            BmEvenStep.deltaWord connection input.syndromes degree iter.start else 0#u64
          if delta = 0#u64 then
            .cont (nextRange iter, finalMeter, connection, previous, saved,
              degree, previousLen, incremented shift, previousDelta)
          else
            let candidate := BmEvenStep.nextDegree degree iter.start
            if input.budget.val < candidate then
              .done (finish input connection previous saved finalMeter (.Ok (.Err .DegreeExceedsBudget)))
            else
              .cont (BmAccepted.expectedAccepted (nextRange iter) finalMeter connection previous saved
                degree (ClosedLeafAdvance.usizeWord candidate) (incremented degree) previousLen shift
                previousDelta delta (2 * degree.val ≤ iter.start.val))

/-- Fuel counts the allowed continuations, so the terminal check still runs
with zero fuel. None denotes a continuation beyond the supplied range. -/
noncomputable def run (input : Input) (fuel : Nat) (state : State) : Option (State × Return) :=
  match step input state with
  | .done result => some (state, result)
  | .cont next =>
    match fuel with
    | 0 => none
    | n + 1 => run input n next

def ActualBmLoop : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    BmDiscrepancy.RawArithmetic kernels → BmDiscrepancy.ReduceArithmetic kernels →
    BmMutable.NativeMul kernels → NativeInverse kernels →
    ∀ (input : Input) (iter : IndexRange) (meter : WorkMeter) (connection previous saved : Slice U64)
      (degree previousLen shift : Usize) (previousDelta : U64),
      let state : State := (iter, meter, connection, previous, saved, degree, previousLen, shift, previousDelta)
      Admitted input state →
      ∃ last result, run input (iter.«end».val - iter.start.val) state = some (last, result) ∧
        locator_loop0 fieldDictionary kernels input.restoreConnection input.restorePrevious input.tail
          input.restoreSaved iter input.syndromes input.budget meter input.cost
          connection previous saved degree previousLen shift previousDelta = .ok result

end BulksketchBridge.BmLoop
