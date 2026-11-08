import BulksketchBridge.BmLocatorResidualSpec
import BulksketchBridge.BmLocator
import BulksketchBridge.BmLoopResidual

namespace BulksketchBridge.BmLocator

open Aeneas.Std BmLoop BmEntry DenseCoefficient RebuiltLfsr
open bulksketch.backend.contract bulksketch.types

set_option maxRecDepth 4096

theorem initial_algebraic (syndromes buffers : Slice U64) (capacity budget : Usize) (meter : WorkMeter)
    (bufferBound : 3 * (capacity.val + 1) ≤ buffers.length) :
    Algebraic (inputs syndromes buffers capacity budget) (initial buffers capacity budget meter) := by
  have restLen := tail_length buffers (capacity.val + 1)
  have connectionRoom : 0 < (prefixSlice buffers (capacity.val + 1)).length := by
    rw [prefix_length]
    omega
  have previousRoom : 0 < (prefixSlice (BmEntry.tail buffers (capacity.val + 1)) (capacity.val + 1)).length := by
    rw [prefix_length]
    omega
  simpa only [Algebraic, inputs, initial, show (0#usize).val = 0 by simp, show (1#usize).val = 1 by simp] using
    BmResidualInvariant.initialized syndromes (prefixSlice buffers (capacity.val + 1))
      (prefixSlice (BmEntry.tail buffers (capacity.val + 1)) (capacity.val + 1)) budget connectionRoom previousRoom

theorem reconstructed_locator_refines : ActualBmReconstructedLocator := by
  intro K kernels raw reduce mul inverse syndromes buffers difference initialSyndromes capacity budget
    meter finalMeter budgetBound bufferBound syndromeBound reconstructed priced input start
  have inputMax : syndromes.length ≤ Usize.max := syndromes.length_ineq
  have endVal : start.1.«end».val = 2 * capacity.val :=
    ClosedLeafAdvance.word_val _ (by omega)
  have startVal : start.1.start.val = 0 := by simp [start, initial]
  have valid : Admitted input start :=
    initial_admitted syndromes buffers capacity budget finalMeter budgetBound bufferBound syndromeBound
  have alg : Algebraic input start := initial_algebraic syndromes buffers capacity budget finalMeter bufferBound
  obtain ⟨last, reply, modeled, _, finalValid, finalAlg, sameEnd, finalOrdered, lastStep, success⟩ :=
    loop_residual_refines kernels raw reduce mul inverse input start difference initialSyndromes
      (2 * capacity.val + 1) reconstructed (by rw [startVal]; exact Nat.zero_le _)
      (by rw [endVal]; omega) valid alg
  rw [endVal, startVal, Nat.sub_zero] at modeled
  obtain ⟨answer, resultEq, native⟩ := locator_refines kernels raw reduce mul inverse
    syndromes capacity budget buffers meter (fun _ => ⟨budgetBound, bufferBound, syndromeBound⟩)
  simp only [result, priced] at resultEq
  change (run input (2 * capacity.val) start).map Prod.snd = some answer at resultEq
  rw [modeled] at resultEq
  have answerEq : reply = answer := Option.some.inj resultEq
  subst answer
  refine ⟨last, reply, modeled, native, finalValid, finalAlg, sameEnd, ?_, lastStep, ?_⟩
  · simpa only [sameEnd, endVal] using finalOrdered
  · intro degree successful
    simpa only [endVal] using success degree successful

end BulksketchBridge.BmLocator
