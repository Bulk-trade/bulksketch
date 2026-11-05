import Arithmetic.Funs
import BulksketchBridge.SpreadSpec
import BulksketchProofs.Field.Spread

/-!
# Functional refinement of the unchanged generated native spread body

This proof relates the byte-identical Charon/Aeneas output to the independently
frozen full-word model. Frontend/standard-scalar/compiler/machine semantics
remain the recorded TCB; no application body or external axiom is substituted.
-/

namespace BulksketchBridge.Spread

open Aeneas Aeneas.Std

private theorem shift16 (word : U64) :
    word <<< (16#i32) = Result.ok (⟨word.bv <<< (16 : Nat)⟩ : U64) := by rfl

private theorem shift8 (word : U64) :
    word <<< (8#i32) = Result.ok (⟨word.bv <<< (8 : Nat)⟩ : U64) := by rfl

private theorem shift4 (word : U64) :
    word <<< (4#i32) = Result.ok (⟨word.bv <<< (4 : Nat)⟩ : U64) := by rfl

private theorem shift2 (word : U64) :
    word <<< (2#i32) = Result.ok (⟨word.bv <<< (2 : Nat)⟩ : U64) := by rfl

private theorem shift1 (word : U64) :
    word <<< (1#i32) = Result.ok (⟨word.bv <<< (1 : Nat)⟩ : U64) := by rfl

/-- Every generated spread call returns the exact complete expected scalar. -/
theorem spread_refines (input : U64) :
    bulksketch.field.gf64.spread input = Result.ok (expectedWord input) := by
  simp only [bulksketch.field.gf64.spread, Aeneas.Std.lift,
    bind_ok, shift16, shift8, shift4, shift2, shift1]
  rfl

/-- The actual generated result has every specified interleaved coefficient. -/
theorem spread_coefficients (input : U64) (index : Nat) (hi : index < 64) :
    ∃ output : U64,
      bulksketch.field.gf64.spread input = Result.ok output ∧
      output.bv.getLsbD index =
        if index % 2 = 0 then input.bv.getLsbD (index / 2) else false := by
  refine ⟨expectedWord input, spread_refines input, ?_⟩
  exact BulksketchProofs.Field.spread64_bits input.bv index hi

end BulksketchBridge.Spread
