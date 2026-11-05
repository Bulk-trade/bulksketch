import Arithmetic.Funs
import BulksketchBridge.SpreadSpec

/-! Frozen universal spread propositions, separated from their proof bodies. -/

namespace BulksketchBridge.SpreadChallenges

open Aeneas Aeneas.Std

/-- Every original generated call returns normally with the exact full word. -/
def normalResultMatchesModel : Prop :=
  ∀ input : U64,
    bulksketch.field.gf64.spread input = Result.ok (Spread.expectedWord input)

/-- All 64 output coefficients agree with interleaving, for every input word. -/
def allCoefficientsMatch : Prop :=
  ∀ (input : U64) (index : Nat), index < 64 →
    ∃ output : U64,
      bulksketch.field.gf64.spread input = Result.ok output ∧
      output.bv.getLsbD index =
        if index % 2 = 0 then input.bv.getLsbD (index / 2) else false

end BulksketchBridge.SpreadChallenges
