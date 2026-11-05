import Arithmetic.Funs
import BulksketchBridge.FrobeniusSpec

/-! Universal actual-source repeated-square proposition, frozen before proof search. -/

namespace BulksketchBridge.FrobeniusChallenges

open Aeneas Aeneas.Std

/-- Every word and every U32 power return normally with every output bit matching
exactly power modulo 64 independent polynomial squarings. -/
def normalResultMatchesIteratedSquare : Prop :=
  ∀ input : U64, ∀ power : U32,
    bulksketch.field.gf64.frobenius
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input power =
        Result.ok (Frobenius.expectedWord input power)

end BulksketchBridge.FrobeniusChallenges
