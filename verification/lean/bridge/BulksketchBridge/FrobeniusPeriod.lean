import BulksketchBridge.FrobeniusPeriodChallenges
import BulksketchBridge.Frobenius
import BulksketchProofs.Field.Period

/-! Algebraic period consequences for the unchanged earlier source model and
native endpoint. The finite-basis proof is independent of irreducibility.
The extraction/runtime/compiler/machine trusted boundary remains unchanged. -/

namespace BulksketchBridge.FrobeniusPeriod

open Aeneas.Std

theorem model_correspondence : ExistingModelMatchesCore := by
  intro count input
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [Frobenius.repeatedSquare, BulksketchProofs.Field.Period.iterateSquare, ih]
    rfl

theorem existing_period64 : ExistingModelPeriod64 := by
  intro input
  rw [model_correspondence]
  exact BulksketchProofs.Field.Period.sixty_four_squares_identity input

theorem existing_iteration_mod64 : ExistingModelModulo64 := by
  intro count input
  rw [model_correspondence, model_correspondence]
  exact BulksketchProofs.Field.Period.iteration_modulo64 count input

/-- The source's modulo64 request equals the unmodded mathematical iteration,
for every input word and every source U32 power. -/
theorem native_unmodded_refines : NativeUnmoddedIteration := by
  intro input power
  rw [Frobenius.frobenius_refines]
  change Result.ok (⟨Frobenius.repeatedSquare (power.val % 64) input.bv⟩ : U64) = _
  rw [model_correspondence, BulksketchProofs.Field.Period.iteration_modulo64]

end BulksketchBridge.FrobeniusPeriod
