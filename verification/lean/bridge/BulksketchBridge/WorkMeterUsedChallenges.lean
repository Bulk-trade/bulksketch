import Workmeter.Funs
import BulksketchBridge.WorkMeterSpec

/-!
Frozen claim for the original Rust WorkMeter::used getter, across every state.
`impl.used` is the extracted Rust method; `meter.used` is the state projection.
The equality establishes normal return and its exact field value. Shared-reference
memory framing remains in the stated frontend/runtime trust boundary.
-/
namespace BulksketchBridge.Challenges

open Aeneas Aeneas.Std BulksketchBridge.WorkMeter

def generatedUsedMatchesExactValue : Prop :=
  ∀ (meter : GeneratedMeter),
    bulksketch.types.WorkMeter.impl.used meter = Aeneas.Std.Result.ok meter.used ∧
    toUInt64 meter.used = (toModel meter).used

end BulksketchBridge.Challenges
