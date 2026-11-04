import Arithmetic.Funs
import BulksketchBridge.MapsCanonicalTraceSpec

/-! Independent whole-byte fallback-trace contract, frozen before proof search. -/

namespace BulksketchBridge.MapsCanonicalTraceChallenges

open Aeneas Aeneas.Std

def normalResultMatchesAbsoluteTrace : Prop :=
  ∀ input : U64,
    bulksketch.field.maps.canonical_trace
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input =
        Result.ok (MapsCanonicalTrace.expectedWord input)

end BulksketchBridge.MapsCanonicalTraceChallenges
