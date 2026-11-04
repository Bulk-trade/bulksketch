import Workmeter.Types
import BulksketchProofs.Resource.WorkMeterSpec

/-!
# Stable generated-body WorkMeter correspondence definitions

These handwritten mappings preserve every generated state field and all 64
scalar bits. They state the comparison with the existing finite-word resource
model; proofs live in `BulksketchBridge.WorkMeter`.

The generated types and concrete runtime models are imported unchanged. The
Charon/Aeneas frontend, Rust standard-library model correspondence, compiler,
and machine-semantics trust boundaries remain explicit separate obligations.
-/

namespace BulksketchBridge.WorkMeter

open Aeneas Aeneas.Std

abbrev GeneratedMeter := bulksketch.types.WorkMeter
abbrev ModelMeter := BulksketchProofs.Resource.WorkMeter

/-- Preserve all 64 bits when moving from Aeneas U64 to Lean's UInt64. -/
def toUInt64 (word : U64) : UInt64 := UInt64.ofBitVec word.bv

/-- The generated state and the handwritten state have the same three fields. -/
def toModel (meter : GeneratedMeter) : ModelMeter :=
  { limit := toUInt64 meter.limit, used := toUInt64 meter.used,
    exhausted := meter.exhausted }

/-- Map a model success bit to the exact application-level Rust result. -/
def rustOutcome (success : Bool) :
    Aeneas.Std.core.result.Result Unit bulksketch.types.DecodeError :=
  if success then .Ok () else .Err .WorkLimitExceeded

end BulksketchBridge.WorkMeter
