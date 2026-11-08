import BulksketchBridge.BmLoopSpec
import BulksketchBridge.BmResidualInvariant

namespace BulksketchBridge.BmLoop

open Aeneas.Std BmStepControl

def Algebraic (input : Input) : State → Prop
  | (iter, _, connection, previous, _, degree, previousLen, shift, scale) =>
      BmResidualInvariant.Invariant input.syndromes connection previous iter.start.val
        degree.val previousLen.val shift.val scale

/-- When the native loop starts from an admitted reconstructed prefix, its
last state still satisfies the exact scalar, residual and anchor invariants.
A failure may stop at an active index; successful completion reaches the
original exclusive stop. -/
def ActualBmLoopResidual : Prop :=
  ∀ {K : Type} (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64),
    BmDiscrepancy.RawArithmetic kernels → BmDiscrepancy.ReduceArithmetic kernels →
    BmMutable.NativeMul kernels → BmTerminal.NativeInverse kernels →
    ∀ (input : Input) (state : State) (difference initial : Slice U64) (processed : Nat),
      Reconstruction.Prefix difference initial input.syndromes processed →
      state.1.start.val ≤ state.1.«end».val →
      state.1.«end».val < processed → Admitted input state → Algebraic input state →
      ∃ last reply, run input (state.1.«end».val - state.1.start.val) state = some (last, reply) ∧
        (let (iter, meter, connection, previous, saved, degree, previousLen, shift, scale) := state
         bulksketch.decode.bm.locator_loop0 BmDiscrepancy.fieldDictionary kernels input.restoreConnection
           input.restorePrevious input.tail input.restoreSaved iter input.syndromes input.budget meter
           input.cost connection previous saved degree previousLen shift scale) = .ok reply ∧
        Admitted input last ∧ Algebraic input last ∧ last.1.«end» = state.1.«end» ∧
        last.1.start.val ≤ last.1.«end».val ∧ step input last = .done reply ∧
        (∀ degree, reply.1 = .Ok (.Ok degree) → last.1.start.val = state.1.«end».val)

end BulksketchBridge.BmLoop
