import Workmeter.Funs
import BulksketchBridge.WorkMeterSpec

/-! Fixed claims over the unchanged actual Rust-generated bodies. -/

namespace BulksketchBridge.Challenges

open Aeneas Aeneas.Std BulksketchBridge.WorkMeter

def generatedConstructorMatchesModel : Prop :=
  ∀ (limit : U64), ∃ final : GeneratedMeter,
    bulksketch.types.WorkMeter.new limit = Aeneas.Std.Result.ok final ∧
    toModel final = BulksketchProofs.Resource.WorkMeter.new (toUInt64 limit)

def generatedChargeMatchesExactResultAndState : Prop :=
  ∀ (meter : GeneratedMeter) (amount : U64), ∃ final : GeneratedMeter,
    bulksketch.types.WorkMeter.charge meter amount =
      Aeneas.Std.Result.ok
        (rustOutcome ((toModel meter).charge (toUInt64 amount)).2, final) ∧
    toModel final = ((toModel meter).charge (toUInt64 amount)).1

def stateProjectionLosesNothing : Prop := Function.Injective toModel

end BulksketchBridge.Challenges
