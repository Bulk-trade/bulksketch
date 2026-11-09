import BulksketchBridge.AvxHorizontalXor
import BulksketchBridge.AvxSquareRows
import BulksketchBridge.Algebra.WordOps

namespace BulksketchBridge.AvxTileSyndrome

open Aeneas.Std Aeneas.Std.Avx512Register
open Algebra.Gf64 Avx512RegisterChallenges
open bulksketch.backend.x86_vpclmul512

def step (base : Word512) : Nat → Word512
  | 0 => base
  | row + 1 => productsReduced (step base row) (productsReduced base base)

theorem step_exact (mode : Bool) (base : Word512) (row : Nat) :
    multiply mode (step base row) (productsReduced base base) =
      Result.ok (step base (row + 1)) :=
  Avx512Register.multiply_refines _ _ _

theorem step_field (base : Word512) (pair : Fin 4) (high : Bool) (row : Nat) :
    toField (step base row pair high) = toField (base pair high) ^ (2 * row + 1) := by
  induction row with
  | zero => simp [step]
  | succ row ih =>
    simp only [step, productsReduced, toField_mul] at *
    rw [ih, ← pow_two, ← pow_add]
    congr 1

def xorRegister (a b : Word512) : Word512 := fun pair high => a pair high ^^^ b pair high

noncomputable def registerFieldSum (value : Fin 4 → Bool → Field) : Field :=
  ((value 0 false + value 2 false) + (value 1 false + value 3 false)) +
  ((value 0 true + value 2 true) + (value 1 true + value 3 true))

theorem parity_field (value : Word512) :
    toField (AvxHorizontalXor.parity value) = registerFieldSum (fun p h => toField (value p h)) := by
  simp only [AvxHorizontalXor.parity, registerFieldSum, toField_xor]

theorem parity_sum_registers (a b : Word512) :
    toField (AvxHorizontalXor.parity (xorRegister a b)) =
      toField (AvxHorizontalXor.parity a) + toField (AvxHorizontalXor.parity b) := by
  simp only [parity_field, xorRegister, toField_xor, registerFieldSum]
  abel

def reduceTile : List Word512 → Word512
  | [] => fun _ _ => 0
  | first :: rest => xorRegister first (reduceTile rest)

theorem row_field (bases : List Word512) (row : Nat) :
    toField (AvxHorizontalXor.parity (reduceTile (bases.map (fun base => step base row)))) =
      (bases.map (fun base => registerFieldSum (fun pair high => toField (base pair high) ^ (2 * row + 1)))).sum := by
  induction bases with
  | nil =>
    simp only [List.map_nil, reduceTile, parity_field, registerFieldSum, toField_zero, add_zero, List.sum_nil]
  | cons base rest ih =>
    simp only [List.map_cons, reduceTile, parity_sum_registers, ih, List.sum_cons]
    rw [parity_field]
    simp only [step_field]


open scoped BigOperators

theorem registerFieldSum_flat (value : Fin 8 → Field) :
    registerFieldSum (fun pair high => value (X86MaskedMemory.flatIndex pair high)) =
      ∑ lane : Fin 8, value lane := by
  simp only [registerFieldSum, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (value 0 + value 4 + (value 2 + value 6)) +
      (value 1 + value 5 + (value 3 + value 7)) =
      value 0 + (value 1 + (value 2 + (value 3 + (value 4 + (value 5 + (value 6 + (value 7 + 0)))))))
  abel

theorem loaded_row_field (chunks : List (Slice U64)) (row : Nat) :
    toField (AvxHorizontalXor.parity
      (reduceTile (chunks.map (fun chunk => step (AvxSquare.loadWords chunk) row)))) =
      (chunks.map (fun chunk =>
        ∑ lane : Fin 8, if lane.val < chunk.length then toField chunk[lane.val]!.bv ^ (2 * row + 1) else 0)).sum := by
  have same : (chunks.map AvxSquare.loadWords).map (fun base => step base row) =
      chunks.map (fun chunk => step (AvxSquare.loadWords chunk) row) := by
    rw [List.map_map]
    rfl
  rw [← same, row_field, List.map_map]
  congr 1
  apply congrArg (fun f => chunks.map f)
  funext chunk
  simp only [Function.comp_apply]
  rw [show (fun p h => toField (AvxSquare.loadWords chunk p h) ^ (2 * row + 1)) =
    (fun p h => (fun lane : Fin 8 =>
      if lane.val < chunk.length then toField chunk[lane.val]!.bv ^ (2 * row + 1) else 0)
      (X86MaskedMemory.flatIndex p h)) by
    funext pair high
    simp only [AvxSquare.loadWords]
    split
    · rfl
    · rw [toField_zero, zero_pow (by omega)]]
  exact registerFieldSum_flat (fun lane =>
    if lane.val < chunk.length then toField chunk[lane.val]!.bv ^ (2 * row + 1) else 0)

#print axioms loaded_row_field

end BulksketchBridge.AvxTileSyndrome
