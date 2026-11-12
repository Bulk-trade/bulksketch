import Arithmetic.SumCostsGenerated
import BulksketchBridge.RowWorkBudgetV1

namespace BulksketchBridge.RootWorkBudget

open Aeneas Aeneas.Std WorkSchedule
open bulksketch bulksketch.decode.work bulksketch.types
open core.result.Result.Insts

abbrev sumClosure :=
  decode.work.sum_costs.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0ChargeResultU64DecodeError.call_mut

private noncomputable def sumStep (total : U64) (charge : Charge) : Result CostResult := do
  let priced ← WorkScheduleV1.cost charge
  match priced with
  | .Err error => .ok (.Err error)
  | .Ok amount => add total amount

theorem native_sum_closure (total : U64) (charge : Charge) :
    decode.work.sum_costs.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0ChargeResultU64DecodeError.call_mut
      () (total, charge) = (do
      let result ← sumStep total charge
      .ok (result, ())) := by
  unfold sumStep
  unfold decode.work.sum_costs.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0ChargeResultU64DecodeError.call_mut
  simp only [Aeneas.Std.bind_assoc]
  apply congrArg (fun continuation => Aeneas.Std.bind (WorkScheduleV1.cost charge) continuation)
  funext result
  cases result <;> simp [CoreOpsTry.branch, bind_ok,
    CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]

private theorem fold_costs_cons (charge : Charge) (tail : List Charge) (total : U64) :
    foldCosts (charge :: tail) total = (do
      let result ← sumStep total charge
      match result with
      | .Err error => .ok (.Err error)
      | .Ok next => foldCosts tail next) := by
  rw [foldCosts]
  unfold sumStep
  simp only [Aeneas.Std.bind_assoc]
  apply congrArg (fun continuation => Aeneas.Std.bind (WorkScheduleV1.cost charge) continuation)
  funext result
  cases result <;> first | rfl | simp only [bind_ok]

theorem native_fold_returns_original_cost (charges : List Charge) (total : U64) (cursor : Nat) :
    (do
      let (result, _) ← sumCostsTryFoldFrom charges total cursor ()
      .ok result) = foldCosts charges total := by
  induction charges generalizing total cursor with
  | nil =>
    simp only [sumCostsTryFoldFrom, foldCosts, bind_ok]
    rfl
  | cons charge tail ih =>
    simp only [sumCostsTryFoldFrom, fold_costs_cons, native_sum_closure, Aeneas.Std.bind_assoc, bind_ok]
    apply congrArg (fun continuation => Aeneas.Std.bind (sumStep total charge) continuation)
    funext result
    cases result with
    | Err reason =>
      change Aeneas.Std.bind (Result.ok ((.Err reason : CostResult), cursor + 1))
        (fun pair => Result.ok pair.1) = _
      exact bind_ok _ _
    | Ok next => exact ih next (cursor + 1)

/-- The checked iterator consumes the failing charge exactly once and
    does not invoke a later callback after the first error. -/
inductive SumFoldTrace : List Charge → U64 → CostResult → Nat → Prop where
  | empty (total : U64) : SumFoldTrace [] total (.Ok total) 0
  | rejected {charge tail total error} :
      sumStep total charge = .ok (.Err error) →
      SumFoldTrace (charge :: tail) total (.Err error) 1
  | continued {charge tail total next result used} :
      sumStep total charge = .ok (.Ok next) →
      SumFoldTrace tail next result used →
      SumFoldTrace (charge :: tail) total result (used + 1)

theorem native_fold_cursor {charges total result used} (trace : SumFoldTrace charges total result used)
    (cursor : Nat) :
    sumCostsTryFoldFrom charges total cursor () = .ok (result, cursor + used) := by
  induction trace generalizing cursor with
  | empty total => rfl
  | rejected price =>
    simp only [sumCostsTryFoldFrom, native_sum_closure, price, bind_ok]
    rfl
  | @continued charge tail total next result used price trace ih =>
    simp only [sumCostsTryFoldFrom, native_sum_closure, price, bind_ok]
    change sumCostsTryFoldFrom tail next (cursor + 1) () = _
    rw [ih, show cursor + 1 + used = cursor + (used + 1) by omega]

/-- A single execution of the pinned Rust default try_fold loop reads
    the stock slice iterator's next element before invoking the original
    callback and returns immediately on that callback's first error. -/
theorem native_try_fold_step (iter : core.slice.iter.Iter Charge) (total : U64) :
    decode.work.checked_sum_costs_slice_try_fold iter total () = (do
      let (item, next) ← core.slice.iter.IteratorSliceIter.next iter
      match item with
      | none => .ok (.Ok total, next)
      | some charge =>
        let (priced, _) ← sumClosure () (total, charge)
        match priced with
        | .Err reason => .ok (.Err reason, next)
        | .Ok running => decode.work.checked_sum_costs_slice_try_fold next running ()) := by
  unfold decode.work.checked_sum_costs_slice_try_fold
  unfold core.slice.iter.IteratorSliceIter.next
  split
  · rename_i inside
    have valid : iter.i < iter.slice.val.length := by simpa only [Slice.len_val] using inside
    have drop := List.drop_eq_getElem_cons valid
    simp only [drop, sumCostsTryFoldFrom, bind_ok, Aeneas.Std.bind_assoc]
    apply congrArg (fun continuation => Aeneas.Std.bind (sumClosure () (total, iter.slice.val[iter.i])) continuation)
    funext value
    obtain ⟨result, closure⟩ := value
    cases closure
    cases result with
    | Err reason =>
      change Aeneas.Std.bind (Result.ok ((.Err reason : CostResult), iter.i + 1))
        (fun pair => Result.ok (pair.1, {iter with i := pair.2})) = _
      exact bind_ok _ _
    | Ok => rfl
  · rename_i outside
    have beyond : ¬ iter.i < iter.slice.val.length := by simpa only [Slice.len_val] using outside
    have empty : iter.slice.val.drop iter.i = [] :=
      List.drop_eq_nil_iff.mpr (Nat.le_of_not_gt beyond)
    simp only [empty, sumCostsTryFoldFrom, bind_ok]
    cases iter
    rfl

def ActualNativeSumCosts : Prop := SumCostsRefines decode.work.sum_costs

theorem native_sum_costs : ActualNativeSumCosts := by
  intro charges
  simp only [decode.work.sum_costs, core.slice.Slice.iter, decode.work.checked_sum_costs_slice_try_fold,
    bind_ok, Aeneas.Std.bind_assoc, List.drop_zero]
  rw [← native_fold_returns_original_cost charges.val 0#u64 0]
  apply congrArg (fun continuation => Aeneas.Std.bind (sumCostsTryFoldFrom charges.val 0#u64 0 ()) continuation)
  funext value
  rcases value with ⟨result, cursor⟩
  change Aeneas.Std.bind
    (Result.ok (result, (⟨charges, cursor⟩ : core.slice.iter.Iter Charge)))
    (fun pair => Result.ok pair.1) = _
  exact bind_ok _ _

#print axioms native_try_fold_step
#print axioms native_sum_costs
#print axioms native_fold_cursor

end BulksketchBridge.RootWorkBudget
