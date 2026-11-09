import BulksketchBridge.AvxTileRowMath

namespace BulksketchBridge.AvxTileOutputMath

open Aeneas Aeneas.Std
open Aeneas.Std.Avx512Register
open BulksketchBridge.AvxTileSyndrome BulksketchBridge.AvxTileSyndromeLoop
open BulksketchBridge.AvxTileRowMath BulksketchBridge.AvxTileNative
open BulksketchBridge.AvxTileDoubleZip BulksketchBridge.Avx512RegisterChallenges

set_option maxHeartbeats 2600000

def rowWord (bases : List Word512) (row : Nat) : U64 :=
  ⟨AvxHorizontalXor.parity (reduceTile (bases.map (fun base => step base row)))⟩

def transform (bases : List Word512) : Nat → List U64 → List U64
  | _, [] => []
  | row, word :: rest => (word ^^^ rowWord bases row) :: transform bases (row + 1) rest

theorem transform_length (bases : List Word512) (row : Nat) (words : List U64) :
    (transform bases row words).length = words.length := by
  induction words generalizing row with
  | nil => rfl
  | cons first rest ih => simp [transform, ih]

def outputFrame (bases : List Word512) (odd : Slice U64) (cursor row : Nat)
    (bound : cursor ≤ odd.length) : OddIter :=
  ⟨Slice.from (odd.val.take cursor ++ transform bases row (odd.val.drop cursor)) (by
      rw [List.length_append, transform_length, List.length_take, List.length_drop]
      have room : cursor ≤ odd.val.length := bound
      rw [Nat.min_eq_left room, Nat.add_sub_of_le room]
      exact odd.length_ineq), odd.length⟩

theorem restore_one (bases : List Word512) (odd : Slice U64) (cursor row : Nat)
    (more : cursor < odd.length) :
    overwrite cursor (outputFrame bases odd (cursor + 1) (row + 1) (by omega))
      (some (odd[cursor]! ^^^ rowWord bases row)) =
    outputFrame bases odd cursor row (by omega) := by
  have slice :
      (outputFrame bases odd (cursor + 1) (row + 1) (by omega)).slice.setAtNat
        cursor (odd[cursor]! ^^^ rowWord bases row) =
      (outputFrame bases odd cursor row (by omega)).slice := by
    apply Slice.ext
    simp only [outputFrame, Slice.setAtNat, Slice.from_val]
    have bound : cursor < odd.val.length := more
    rw [List.take_succ_eq_append_getElem bound, List.append_assoc]
    simp only [List.singleton_append]
    rw [List.set_append_right cursor _ (by simp only [List.length_take]; omega),
      List.length_take, Nat.min_eq_left (by omega), Nat.sub_self,
      List.drop_eq_getElem_cons bound]
    change _ = odd.val.take cursor ++ ((odd.val[cursor] ^^^ rowWord bases row) ::
      transform bases (row + 1) (odd.val.drop (cursor + 1)))
    rw [Slice.getElem!_Nat_eq, ← List.Inhabited_getElem_eq_getElem! _ _ bound]
    rfl
  unfold overwrite
  dsimp! only
  rw [slice]
  rfl

/-- Original later-syndrome loop applies the register row schedule in order
and restores only the exact odd slice positions through saved callbacks. -/
theorem row_writes_math {W : Usize} (bases : List Word512) (odd : Slice U64)
    (cursor : Nat) (bound : cursor ≤ odd.length) (row : Nat) (back : OddBack)
    (powers steps : Array Word512 W)
    (powersExact : powers.val = bases.map (fun base => step base row))
    (stepsExact : steps.val = bases.map (fun base => productsReduced base base)) :
    let output := rowWrites zero steps (odd.length - cursor) ⟨odd, cursor⟩ back powers
    output.2 output.1 = back (outputFrame bases odd cursor (row + 1) bound) := by
  suffices ∀ fuel cursor (bound : cursor ≤ odd.length), odd.length - cursor = fuel →
    ∀ row back (powers : Array Word512 W), powers.val = bases.map (fun base => step base row) →
    let output := rowWrites zero steps fuel ⟨odd, cursor⟩ back powers
    output.2 output.1 = back (outputFrame bases odd cursor (row + 1) bound) from
    this _ _ bound rfl row back powers powersExact
  intro fuel
  induction fuel with
  | zero =>
    intro cursor bound empty row back powers exactPowers
    have atEnd : cursor = odd.length := by omega
    subst cursor
    have frame : outputFrame bases odd odd.length (row + 1) (by omega) =
        (⟨odd, odd.length⟩ : OddIter) := by
      have slice : (outputFrame bases odd odd.length (row + 1) (by omega)).slice = odd := by
        apply Slice.ext
        simp [outputFrame, Slice.length, transform]
      unfold outputFrame at slice ⊢
      dsimp! only at slice
      rw [slice]
    simp only [rowWrites, frame]
  | succ fuel ih =>
    intro cursor bound count row back powers exactPowers
    have more : cursor < odd.length := by omega
    obtain ⟨nextWord, nextPowers⟩ := row_schedule bases row powers steps exactPowers stepsExact
    have wordExact : (rowUpdate zero powers steps).1 = rowWord bases (row + 1) :=
      U64.bv_eq_imp_eq _ _ nextWord
    have recurrence := ih (cursor + 1) (by omega) (by omega) (row + 1)
      (fun later => back (overwrite cursor later (some (odd[cursor]! ^^^ rowWord bases (row + 1)))))
      (rowUpdate zero powers steps).2 nextPowers
    simp only [rowWrites, ite_eq_left more]
    dsimp! only
    rw [wordExact]
    exact recurrence.trans (congrArg back (restore_one bases odd cursor (row + 1) more))

#print axioms row_writes_math

end BulksketchBridge.AvxTileOutputMath
