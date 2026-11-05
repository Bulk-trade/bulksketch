import Arithmetic.Funs
import BulksketchBridge.MapsTraceSpec

/-! Universal native trace normal-return proposition, frozen before proof search. -/

namespace BulksketchBridge.MapsTraceChallenges

open Aeneas Aeneas.Std

/-- The real extracted Gf64 instance returns the complete expected byte for every word. -/
def normalResultMatchesSelector : Prop :=
  ∀ input : U64,
    bulksketch.field.maps.trace
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input =
        Result.ok (MapsTrace.expectedWord input)

end BulksketchBridge.MapsTraceChallenges
