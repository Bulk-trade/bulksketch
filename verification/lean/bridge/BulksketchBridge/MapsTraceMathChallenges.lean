import Arithmetic.Funs
import BulksketchProofs.Field.MapsSpec

namespace BulksketchBridge.MapsTraceMathChallenges

open Aeneas Aeneas.Std

/-- The full native byte, zero-extended without loss, is the independent absolute
trace (all64 conjugates), and its value is always a single bit. -/
def actualTraceMatchesAbsoluteTrace : Prop :=
  ∀ input : U64, ∃ output : U8,
    bulksketch.field.maps.trace
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input = Result.ok output ∧
    output.bv.setWidth 64 = BulksketchProofs.Field.Maps.absoluteTrace input.bv ∧
    output.val ≤ 1

end BulksketchBridge.MapsTraceMathChallenges
