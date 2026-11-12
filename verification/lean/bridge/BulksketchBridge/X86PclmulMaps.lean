import BulksketchBridge.X86PclmulMapsChallenges
import BulksketchBridge.X86Pclmul
import BulksketchBridge.FrobeniusLookup
import BulksketchBridge.FrobeniusPeriod
import BulksketchBridge.MapsQuadratic

namespace BulksketchBridge.X86PclmulMaps

open Aeneas Aeneas.Std BulksketchProofs.Field.Period
open X86PclmulMapsChallenges bulksketch.backend.x86_pclmul

/-- Both reduction selectors implement the same square. -/
theorem multiply_square_refines (selector : Bool) (input : U64) :
    multiply selector dictionary input input = Result.ok (Square.expectedWord input) := by
  have selected := X86Pclmul.square_refines input
  change multiply true dictionary input input = _ at selected
  rw [X86Pclmul.multiply_refines true input input] at selected
  rw [X86Pclmul.multiply_refines selector input input]
  exact selected

private theorem square_matches (input : U64) :
    multiply false dictionary input input = bulksketch.field.gf64.square dictionary input := by
  rw [multiply_square_refines, Square.square_refines]

/-- The two lowered loop copies use the same checked range step and square
as the original verified portable loop. -/
private theorem loop_body_matches :
    (fun (state : core.ops.range.Range U32 × U64) =>
      frobenius_loop0.body dictionary state.1 state.2) =
    (fun state => bulksketch.field.gf64.frobenius_loop.body dictionary state.1 state.2) := by
  funext state
  rcases state with ⟨range, word⟩
  simp only [frobenius_loop0.body, bulksketch.field.gf64.frobenius_loop.body, square_matches]
  rfl

theorem frobenius_loop0_refines (range : core.ops.range.Range U32) (input : U64)
    (ordered : range.start.val ≤ range.«end».val) (bounded : range.«end».val ≤ 63) :
    frobenius_loop0 dictionary range input =
      Result.ok (⟨iterateSquare (range.«end».val - range.start.val) input.bv⟩ : U64) := by
  unfold frobenius_loop0
  rw [loop_body_matches]
  change bulksketch.field.gf64.frobenius_loop dictionary range input = _
  have model := FrobeniusPeriod.model_correspondence (range.«end».val - range.start.val) input.bv
  simpa only [model] using Frobenius.loop_refines range input ordered bounded

theorem frobenius_loop1_refines (range : core.ops.range.Range U32) (input : U64)
    (ordered : range.start.val ≤ range.«end».val) (bounded : range.«end».val ≤ 63) :
    frobenius_loop1 dictionary range input =
      Result.ok (⟨iterateSquare (range.«end».val - range.start.val) input.bv⟩ : U64) :=
  frobenius_loop0_refines range input ordered bounded

/-- Includes table hits and the fallback iteration on every U32 request. -/
theorem frobenius_refines : FrobeniusRefines := by
  intro input power
  obtain ⟨remainder, remainderNormal, remainderValue⟩ := RawMulTable.normal_of_spec _ _
    (U32.rem_spec power (y := 64#u32) (by decide))
  change remainder.val = power.val % 64 at remainderValue
  have bounded : remainder.val ≤ 63 := by
    have bound := Nat.mod_lt power.val (by decide : 0 < 64)
    omega
  have complete : iterateSquare remainder.val input.bv = iterateSquare power.val input.bv := by
    rw [remainderValue, iteration_modulo64]
  have hit := FrobeniusTable.lookup_refines input remainder
  have fallback := frobenius_loop0_refines { start := 0#u32, «end» := remainder } input
    (by simp) bounded
  simp only [bulksketch.backend.x86_pclmul.frobenius,
    bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS,
    bind_ok, ite_true, remainderNormal, hit]
  by_cases supported : remainder.val ∈ FrobeniusTable.powers
  · simp only [ite_eq_left supported, complete]
  · simpa only [ite_eq_right supported, show (0#u32).val = 0 by rfl, Nat.sub_zero, complete] using fallback

theorem frobenius_entry_refines : FrobeniusEntryRefines := by
  intro input power
  exact frobenius_refines input power

/-- The hardware square preserves the original trace branch and assertion. -/
theorem solve_quadratic_refines : SolveQuadraticRefines := by
  intro input
  have identical : solve_quadratic dictionary input =
      bulksketch.field.maps.solve_quadratic dictionary input := by
    simp only [solve_quadratic, bulksketch.field.maps.solve_quadratic, square_matches]
  rw [identical]
  exact MapsQuadratic.solve_quadratic_refines input

theorem solve_quadratic_entry_refines : SolveQuadraticEntryRefines := by
  intro input
  exact solve_quadratic_refines input

end BulksketchBridge.X86PclmulMaps
