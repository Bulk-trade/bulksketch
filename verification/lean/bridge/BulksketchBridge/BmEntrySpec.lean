import Arithmetic.BmLocatorGenerated
import BulksketchBridge.BmPriceSpec
import BulksketchBridge.StageChargeSpec
import BulksketchBridge.RebuiltLfsrSpec

namespace BulksketchBridge.BmEntry

open Aeneas.Std DenseCoefficient RebuiltLfsr
open bulksketch.backend.contract bulksketch.decode.bm bulksketch.types

abbrev fieldDictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
abbrev Reply := core.result.Result (core.result.Result Usize DecodeFailure) DecodeError
abbrev Return := Reply × Slice U64 × WorkMeter

def tail (words : Slice U64) (split : Nat) : Slice U64 :=
  Slice.from (words.val.drop split) ((List.drop_length_is_le split words.val).trans words.length_ineq)

/-- The original split continuation accepts both pieces of the original
lengths. A different-length replacement falls back to the original buffer. -/
def splitBack (original : Slice U64) (split : Nat) (parts : Slice U64 × Slice U64) : Slice U64 :=
  if lengths : parts.1.length = min split original.length ∧
      parts.2.length = original.length - split then
    Slice.from (parts.1.val ++ parts.2.val) (by
      have upper := Slice.length_ineq original
      change original.length ≤ Usize.max at upper
      simp only [List.length_append]
      change parts.1.length + parts.2.length ≤ Usize.max
      omega)
  else original

def initialBuffer (original : Slice U64) (budget : Usize) : Slice U64 :=
  (restorePrefix original (zeroWords (prefixSlice original (budget.val + 1)))).setAtNat 0 1#u64

def pricing (meter : WorkMeter) (budget : Usize) :=
  StageCharge.chargeResult meter (WorkSchedule.checkedCost (BmPrice.bmUnits budget))

/-- All entry writes and early charge outcomes, with the original outer
loop as the continuation. The outer recurrence is a separate obligation. -/
def expectedEntry {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (syndromes : Slice U64) (capacity budget : Usize) (buffers : Slice U64) (meter : WorkMeter) :
    Result Return := do
  let (charge, finalMeter) := pricing meter budget
  match charge with
  | .Err error => .ok (.Err error, buffers, finalMeter)
  | .Ok () =>
    let width ← capacity + 1#usize
    let stop ← 2#usize * capacity
    let rest := tail buffers width.val
    let rest1 := tail rest width.val
    locator_loop0 fieldDictionary kernels (splitBack buffers width.val) (splitBack rest width.val)
      (tail rest1 width.val) (splitBack rest1 width.val) ⟨0#usize, stop⟩ syndromes budget finalMeter
      ⟨BitVec.ofNat 64 (BmPrice.bmUnits budget)⟩ (initialBuffer (prefixSlice buffers width.val) budget)
      (initialBuffer (prefixSlice rest width.val) budget) (prefixSlice rest1 width.val)
      0#usize 1#usize 1#usize 1#u64

def ActualBmEntryRefines : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (syndromes : Slice U64) (capacity budget : Usize) (buffers : Slice U64) (meter : WorkMeter),
    ((pricing meter budget).1 = .Ok () →
      budget.val ≤ capacity.val ∧ 3 * (capacity.val + 1) ≤ buffers.length) →
    locator fieldDictionary kernels syndromes capacity budget buffers meter =
      expectedEntry kernels syndromes capacity budget buffers meter

end BulksketchBridge.BmEntry
