import BulksketchBridge.ReconstructionPowerSumsSpec
import BulksketchBridge.Reconstruction
import BulksketchBridge.SyndromeUniqueness
import BulksketchBridge.Algebra.WordSquare

namespace BulksketchBridge.Reconstruction

open Aeneas.Std Algebra.Gf64 Reconciliation

/-- When the input is the odd syndrome row of a support, the native
recurrence represents all positive power sums through twice its capacity. -/
theorem prefix_represents_power_sums (roots : Finset Algebra.Gf64.Field)
    (difference initial syndromes : Slice U64)
    (oddInput : ∀ i < difference.length, toField difference.val[i]!.bv = oddSyndrome roots i)
    (inv : Prefix difference initial syndromes (2 * difference.length + 1)) :
    ∀ p, 0 < p → p ≤ 2 * difference.length → toField syndromes.val[p]!.bv = powerSum roots p := by
  let _ : CharP Algebra.Gf64.Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
    intro positive bounded
    have step := inv.recurrence p positive (by omega)
    by_cases even : p % 2 = 0
    · simp only [SyndromeStep, even, ite_true] at step
      rw [step]
      change toField (BulksketchProofs.Field.Period.squareWord syndromes.val[p / 2]!.bv) = _
      rw [toField_square, ih (p / 2) (by omega) (by omega) (by omega)]
      calc
        powerSum roots (p / 2) ^ 2 = powerSum roots (p / 2 * 2) :=
          (powerSum_even roots (p / 2)).symm
        _ = powerSum roots p := by congr 1; omega
    · simp only [SyndromeStep, even, ite_false] at step
      rw [step, oddInput (p / 2) (by omega), oddSyndrome]
      congr 1
      omega

theorem reconstruct_returns_power_sums : ActualReconstructionReturnsPowerSums := by
  intro F K field kernels self input workspace meter roots square paid charged admitted oddInput
  obtain ⟨reply, updated, final, normal, exactResult⟩ :=
    reconstruct_refines field kernels self input workspace meter square
  simp only [paid, ite_false, PaidOutcome, charged, admitted, ite_true] at exactResult
  obtain ⟨_, rfl, syndromes, rfl, inv⟩ := exactResult
  exact ⟨_, final, normal, prefix_represents_power_sums roots input.difference workspace.syndromes
    syndromes oddInput inv⟩

end BulksketchBridge.Reconstruction
