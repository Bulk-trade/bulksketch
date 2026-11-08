import BulksketchBridge.BmEntrySpec
import BulksketchBridge.BmLoopSpec

namespace BulksketchBridge.BmLocator

open Aeneas.Std BmLoop BmEntry DenseCoefficient
open bulksketch.backend.contract bulksketch.decode.bm bulksketch.types

def inputs (syndromes buffers : Slice U64) (capacity budget : Usize) : Input :=
  let width := capacity.val + 1
  let rest := BmEntry.tail buffers width
  let rest1 := BmEntry.tail rest width
  ⟨splitBack buffers width, splitBack rest width, BmEntry.tail rest1 width, splitBack rest1 width,
    syndromes, budget, ⟨BitVec.ofNat 64 (BmPrice.bmUnits budget)⟩⟩

def initial (buffers : Slice U64) (capacity budget : Usize) (meter : WorkMeter) : State :=
  let width := capacity.val + 1
  let rest := BmEntry.tail buffers width
  let rest1 := BmEntry.tail rest width
  (⟨0#usize, ClosedLeafAdvance.usizeWord (2 * capacity.val)⟩, meter,
    initialBuffer (prefixSlice buffers width) budget, initialBuffer (prefixSlice rest width) budget,
    prefixSlice rest1 width, 0#usize, 1#usize, 1#usize, 1#u64)

/-- Exact result for the original charged locator. The model accounts for
the initial price, all per-index charges, three returned scratch regions,
the untouched suffix and every semantic return. -/
noncomputable def result (syndromes buffers : Slice U64) (capacity budget : Usize)
    (meter : WorkMeter) : Option BmTerminal.Return :=
  match pricing meter budget with
  | (.Err error, finalMeter) => some (.Err error, buffers, finalMeter)
  | (.Ok (), finalMeter) =>
    (run (inputs syndromes buffers capacity budget) (2 * capacity.val)
      (initial buffers capacity budget finalMeter)).map Prod.snd

def ActualBmLocator : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    BmDiscrepancy.RawArithmetic kernels → BmDiscrepancy.ReduceArithmetic kernels →
    BmMutable.NativeMul kernels → BmTerminal.NativeInverse kernels →
    ∀ (syndromes : Slice U64) (capacity budget : Usize) (buffers : Slice U64) (meter : WorkMeter),
      ((pricing meter budget).1 = .Ok () →
        budget.val ≤ capacity.val ∧ 3 * (capacity.val + 1) ≤ buffers.length ∧
        2 * capacity.val + 1 ≤ syndromes.length) →
      ∃ reply, result syndromes buffers capacity budget meter = some reply ∧
        locator BmEntry.fieldDictionary kernels syndromes capacity budget buffers meter = .ok reply

end BulksketchBridge.BmLocator
