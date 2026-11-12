import BulksketchBridge.BmLocatorSpec
import BulksketchBridge.BmLoopResidualSpec

namespace BulksketchBridge.BmLocator

open Aeneas.Std BmLoop BmEntry
open bulksketch.backend.contract bulksketch.decode.bm bulksketch.types

/-- The charged original locator carries the exact residual invariant from
its own zeroed scratch through every native step, including odd skips.
The final state is tied to the returned words and meter by the exact
terminal or error step. -/
def ActualBmReconstructedLocator : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    BmDiscrepancy.RawArithmetic kernels → BmDiscrepancy.ReduceArithmetic kernels →
    BmMutable.NativeMul kernels → BmTerminal.NativeInverse kernels →
    ∀ (syndromes buffers difference initialSyndromes : Slice U64) (capacity budget : Usize)
      (meter finalMeter : WorkMeter),
      budget.val ≤ capacity.val → 3 * (capacity.val + 1) ≤ buffers.length →
      2 * capacity.val + 1 ≤ syndromes.length →
      Reconstruction.Prefix difference initialSyndromes syndromes (2 * capacity.val + 1) →
      pricing meter budget = (.Ok (), finalMeter) →
      let input := inputs syndromes buffers capacity budget
      let start := initial buffers capacity budget finalMeter
      ∃ last reply, run input (2 * capacity.val) start = some (last, reply) ∧
        locator BmEntry.fieldDictionary kernels syndromes capacity budget buffers meter = .ok reply ∧
        Admitted input last ∧ Algebraic input last ∧ last.1.«end» = start.1.«end» ∧
        last.1.start.val ≤ 2 * capacity.val ∧ step input last = .done reply ∧
        (∀ degree, reply.1 = .Ok (.Ok degree) → last.1.start.val = 2 * capacity.val)

end BulksketchBridge.BmLocator
