import BulksketchBridge.ExecutionVerifySpec

namespace BulksketchBridge.ExecutionVerify

open Aeneas.Std WorkSchedule
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.row bulksketch.decode.scratch
open bulksketch.types

def checkedNext (units : Nat) (next : Nat → CostResult) : CostResult :=
  match checkedCost units with
  | .Ok value => next value.val
  | .Err error => .Err error

/-- Prices the full verification path in the source's checked evaluation order. -/
def directCost (capacity outputBudget : Usize) : CostResult :=
  checkedNext (2 * outputBudget.val) fun twiceBudget =>
  checkedNext (twiceBudget + 3) fun perWord =>
  checkedNext (perWord * capacity.val) fun wordCost =>
  checkedNext (outputBudget.val + 1) fun outputCost =>
  checkedCost (wordCost + outputCost)

/-- Prices the rebuilt verification path including every intermediate overflow. -/
def rebuiltCost (capacity outputBudget degree : Usize) : CostResult :=
  checkedNext (3 * degree.val) fun tripleDegree =>
  checkedNext (tripleDegree + 4) fun perWord =>
  checkedNext (perWord * capacity.val) fun wordCost =>
  checkedNext (outputBudget.val + 3) fun outputCost =>
  checkedNext (degree.val + outputCost) fun candidateCost =>
  checkedCost (wordCost + candidateCost)

def actualCost {F K : Type} (self : Execution F K) (input : RowInput) : CostResult :=
  if selects self input then rebuiltCost input.difference.len self.budget.total self.roots.count
  else directCost input.difference.len self.budget.total

/-- The original source, with independent checked prices for both verifier
branches. No normality or success assumption is imposed on the price. -/
def ActualExecutionVerifyWithPrices : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (self : Execution bulksketch.field.Gf64 K) (input : RowInput) (workspace : RowWorkspace)
    (meter : WorkMeter) (seed : Slice U64) (continued : Bool),
    Bounds kernels self input workspace meter (actualCost self input) seed continued →
    Execution.verify DegreeProbeRuntime.fieldDictionary kernels self input workspace meter =
      .ok (expected self input workspace meter (actualCost self input) seed continued)

end BulksketchBridge.ExecutionVerify
