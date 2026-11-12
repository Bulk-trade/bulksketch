import BulksketchBridge.AvxTileSyndromeLoop

namespace BulksketchBridge.AvxTilePowerMath

open Aeneas Aeneas.Std
open Aeneas.Std.Avx512Register
open BulksketchBridge.AvxTilePowerLoop BulksketchBridge.AvxTileSyndrome
open BulksketchBridge.Avx512RegisterChallenges

set_option maxHeartbeats 2500000

def tailProducts (left right : Slice Word512) (i : Nat) : List Word512 :=
  List.zipWith productsReduced (left.val.drop i) (right.val.drop i)

theorem products_length (left right : Slice Word512) (same : left.length = right.length) (i : Nat) :
    (tailProducts left right i).length = left.length - i := by
  unfold tailProducts
  simp only [List.length_zipWith, List.length_drop]
  change min (left.length - i) (right.length - i) = _
  rw [← same, Nat.min_self]

def finalState (left right : Slice Word512) (same : left.length = right.length)
    (i : Nat) (bound : i ≤ left.length) : PowerState :=
  ⟨⟨Slice.from (left.val.take i ++ tailProducts left right i) (by
      rw [List.length_append, List.length_take, products_length left right same i]
      have room : i ≤ left.val.length := bound
      rw [Nat.min_eq_left room, Nat.add_sub_of_le bound]
      exact left.length_ineq), left.length⟩, ⟨right, left.length⟩⟩

theorem tail_products_step (left right : Slice Word512) (same : left.length = right.length)
    (i : Nat) (more : i < left.length) :
    tailProducts left right i =
      productsReduced left[i]! right[i]! :: tailProducts left right (i + 1) := by
  have leftBound : i < left.val.length := more
  have rightBound : i < right.val.length := by change i < right.length; omega
  unfold tailProducts
  rw [List.drop_eq_getElem_cons leftBound, List.drop_eq_getElem_cons rightBound]
  simp only [List.zipWith_cons_cons, Slice.getElem!_Nat_eq,
    ← List.Inhabited_getElem_eq_getElem! _ _ leftBound,
    ← List.Inhabited_getElem_eq_getElem! _ _ rightBound]

theorem previous_write (left right : Slice Word512) (same : left.length = right.length)
    (i : Nat) (more : i < left.length) :
    BulksketchBridge.MutableZip.replaceLeft (finalState left right same (i + 1) (by omega))
      i (productsReduced left[i]! right[i]!) =
      finalState left right same i (by omega) := by
  have exactSlice :
      (finalState left right same (i + 1) (by omega)).fst.slice.setAtNat
        i (productsReduced left[i]! right[i]!) =
      (finalState left right same i (by omega)).fst.slice := by
    apply Slice.ext
    simp only [finalState, Slice.setAtNat, Slice.from_val]
    have bounded : i < left.val.length := more
    rw [List.take_succ_eq_append_getElem bounded, List.append_assoc]
    simp only [List.singleton_append]
    rw [List.set_append_right i _ (by simp only [List.length_take]; omega),
      List.length_take, Nat.min_eq_left (by omega), Nat.sub_self, tail_products_step left right same i more]
    rfl
  unfold BulksketchBridge.MutableZip.replaceLeft
  rw [exactSlice]
  rfl

theorem power_writes_math (left right : Slice Word512) (same : left.length = right.length)
    (i : Nat) (bound : i ≤ left.length) (sum : Word512) (back : Back) :
    let result := powerWrites (left.length - i)
      (BulksketchBridge.MutableZip.stateAt left right i) back sum
    result.1 = (tailProducts left right i).foldl xorRegister sum ∧
    result.2.2 result.2.1 = back (finalState left right same i bound) := by
  suffices ∀ fuel i (bound : i ≤ left.length), left.length - i = fuel →
    ∀ sum back, let result := powerWrites fuel (BulksketchBridge.MutableZip.stateAt left right i) back sum
    result.1 = (tailProducts left right i).foldl xorRegister sum ∧
    result.2.2 result.2.1 = back (finalState left right same i bound) from
    this _ _ bound rfl sum back
  intro fuel
  induction fuel with
  | zero =>
    intro i bound empty sum back
    have atEnd : i = left.length := by omega
    subst i
    have productsEmpty : tailProducts left right left.length = [] := by
      apply List.length_eq_zero_iff.mp
      rw [products_length left right same, Nat.sub_self]
    have frame : finalState left right same left.length (by omega) =
        BulksketchBridge.MutableZip.stateAt left right left.length := by
      unfold finalState BulksketchBridge.MutableZip.stateAt
      congr 2
      apply Slice.ext
      simp only [Slice.from_val, productsEmpty, List.append_nil]
      exact List.take_length
    simp only [powerWrites, productsEmpty, List.foldl_nil, frame, and_self]
  | succ fuel ih =>
    intro i bound count sum back
    have more : i < left.length := by omega
    have rightMore : i < right.length := by omega
    let state := BulksketchBridge.MutableZip.stateAt left right i
    have activePair : active state := ⟨more, rightMore⟩
    have step := ih (i + 1) (by omega) (by omega)
      (xorRegister sum (product state))
      (fun later => back (BulksketchBridge.MutableZip.replaceLeft later i (product state)))
    have advanced : advance state = BulksketchBridge.MutableZip.stateAt left right (i + 1) := rfl
    change (let result := powerWrites (fuel + 1) state back sum
      result.1 = _ ∧ result.2.2 result.2.1 = _)
    simp only [powerWrites, ite_eq_left activePair, advanced]
    rw [tail_products_step left right same i more, List.foldl_cons]
    have newFrame := previous_write left right same i more
    exact ⟨step.1, step.2.trans (congrArg back newFrame)⟩

#print axioms power_writes_math

end BulksketchBridge.AvxTilePowerMath
