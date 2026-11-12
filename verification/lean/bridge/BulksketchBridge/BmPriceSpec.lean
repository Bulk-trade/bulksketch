import BulksketchBridge.WorkScheduleSpec

namespace BulksketchBridge.BmPrice

open Aeneas.Std
open bulksketch.decode.work

def CheckedAddRefines : Prop :=
  ∀ left right : U64,
    add left right = .ok (WorkSchedule.checkedCost (left.val + right.val))

def bmUnits (budget : Usize) : Nat := 6 * (budget.val + 1) + 128

/-- Includes overflow of any intermediate source price operation. -/
def ActualBmPriceRefines : Prop :=
  ∀ budget : Usize,
    WorkScheduleV1.cost (.BmStep budget) = .ok (WorkSchedule.checkedCost (bmUnits budget))

end BulksketchBridge.BmPrice
