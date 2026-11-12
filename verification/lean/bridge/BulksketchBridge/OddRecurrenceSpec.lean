import Arithmetic.OddRecurrenceGenerated
import BulksketchBridge.Algebra.WordSpec
import BulksketchBridge.RawMulSpec

/-! The default scalar continuation consumes a nonempty slice of ascending,
already squared locator coefficients. Each reachable lag starts at one. -/

namespace BulksketchBridge.OddRecurrence

open Aeneas.Std BulksketchBridge.Algebra.Gf64
open bulksketch.backend.contract
open scoped BigOperators

abbrev fieldDictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField

def CorrectArithmetic {Backend : Type} (kernels : BulkKernels Backend bulksketch.field.Gf64) : Prop :=
  (∀ left right, kernels.ArithmeticInst.raw_mul left right =
    bulksketch.field.gf64.raw_mul fieldDictionary left right) ∧
  (∀ product, kernels.ArithmeticInst.reduce product =
    bulksketch.field.gf64.reduce fieldDictionary product)

noncomputable def lagTerm (odd squaredLocator : Slice U64) (index lag : Nat) : Field :=
  toField odd[index - lag]!.bv * toField squaredLocator[lag]!.bv

noncomputable def lagSum (odd squaredLocator : Slice U64) (index start count : Nat) : Field :=
  ∑ offset ∈ Finset.range count, lagTerm odd squaredLocator index (start + offset)

noncomputable def continuationMatches (odd squaredLocator : Slice U64) : Prop :=
  ∀ index : Nat, squaredLocator.length - 1 ≤ index → index < odd.length →
    toField odd[index]!.bv = lagSum odd squaredLocator index 1 (squaredLocator.length - 1)

def ActualDefaultMatchesEveryContinuation : Prop :=
  ∀ {Backend : Type} (kernels : BulkKernels Backend bulksketch.field.Gf64)
    (odd squaredLocator : Slice U64),
    CorrectArithmetic kernels → 0 < squaredLocator.length →
      ∃ output : Bool,
        BulkKernels.odd_recurrence_matches.default kernels odd squaredLocator = Result.ok output ∧
        (output = true ↔ continuationMatches odd squaredLocator)

end BulksketchBridge.OddRecurrence
