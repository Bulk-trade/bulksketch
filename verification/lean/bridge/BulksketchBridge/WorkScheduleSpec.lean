import Arithmetic.WorkScheduleGenerated

namespace BulksketchBridge.WorkSchedule

open Aeneas.Std

abbrev CostResult := core.result.Result bulksketch.types.WorkUnits bulksketch.types.DecodeError

/-- A natural cost is returned exactly when it fits the source u64 envelope. -/
def checkedCost (units : Nat) : CostResult :=
  if bounded : units ≤ U64.max then
    .Ok (U64.ofNatCore units (by
      rw [U64.max_eq] at bounded
      change units < 2 ^ 64
      omega))
  else .Err .WorkLimitExceeded

def reconstructCost (capacity : Usize) : CostResult := checkedCost (3 * capacity.val)

def NumberRefines : Prop :=
  ∀ value : Usize, ∃ word : U64,
    bulksketch.decode.work.number value = .ok (.Ok word) ∧ word.val = value.val

def CheckedMultiplyRefines : Prop :=
  ∀ left right : U64, bulksketch.decode.work.mul left right =
    .ok (checkedCost (left.val * right.val))

/-- Exact cost for the reconstruction tag of the original schedule. -/
def ReconstructCostRefines : Prop :=
  ∀ capacity : Usize, bulksketch.decode.work.WorkScheduleV1.cost (.Reconstruct capacity) =
    .ok (reconstructCost capacity)

end BulksketchBridge.WorkSchedule
