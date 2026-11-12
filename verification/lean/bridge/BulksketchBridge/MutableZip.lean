import Arithmetic.MutableZipRuntime

namespace BulksketchBridge.MutableZip

open Aeneas Aeneas.Std

abbrev State := Aeneas.Std.MutableZip.State

def stateAt {T U : Type} (left : Slice T) (right : Slice U) (position : Nat) : State T U :=
  ⟨⟨left, position⟩, ⟨right, position⟩⟩

def replaceLeft {T U : Type} (state : State T U) (position : Nat) (value : T) : State T U :=
  ⟨{ state.fst with slice := state.fst.slice.setAtNat position value }, state.snd⟩

theorem construct {T U : Type} (left : Slice T) (right : Slice U) :
    bulksketch.core.iter.traits.iterator.Iterator.zip.trait_default
      (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT T)
      (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U)
      ⟨left, 0⟩ right = Result.ok (stateAt left right 0, fun state => state.fst) := by
  simp only [bulksketch.core.iter.traits.iterator.Iterator.zip.trait_default,
    Aeneas.Std.MutableZip.construct,
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_ok, stateAt]

/-- Both actual component cursors are bounded before each read. -/
theorem next_some {T U : Type} (state : State T U)
    (leftBound : state.fst.i < state.fst.slice.length)
    (rightBound : state.snd.i < state.snd.slice.length) :
    bulksketch.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT T)
      (core.iter.traits.iterator.IteratorSliceIter U) state =
      Result.ok (some (state.fst.slice[state.fst.i], state.snd.slice[state.snd.i]),
        ⟨{ state.fst with i := state.fst.i + 1 }, { state.snd with i := state.snd.i + 1 }⟩,
        fun later replacement =>
          match replacement with
          | none => later
          | some value => replaceLeft later state.fst.i value.1) := by
  have leftLen : state.fst.i < state.fst.slice.len.val := by simpa using leftBound
  have rightLen : state.snd.i < state.snd.slice.len.val := by simpa using rightBound
  have leftStep : core.slice.iter.IteratorIterMut.next state.fst =
      Result.ok (some (state.fst.slice[state.fst.i]), { state.fst with i := state.fst.i + 1 },
        fun later replacement => match replacement with
          | none => later
          | some value => { later with slice := later.slice.setAtNat state.fst.i value }) := by
    unfold core.slice.iter.IteratorIterMut.next
    split
    · rfl
    · contradiction
  have rightStep : core.slice.iter.IteratorSliceIter.next state.snd =
      Result.ok (some (state.snd.slice[state.snd.i]), { state.snd with i := state.snd.i + 1 }) := by
    unfold core.slice.iter.IteratorSliceIter.next
    split
    · rfl
    · contradiction
  change Aeneas.Std.MutableZip.next core.slice.iter.IteratorIterMut.next
    (core.iter.traits.iterator.IteratorSliceIter U) state = _
  rw [Aeneas.Std.MutableZip.next, ite_eq_left (And.intro leftBound rightBound), leftStep, bind_ok]
  rw [show (core.iter.traits.iterator.IteratorSliceIter U).next state.snd = _ from rightStep]
  simp only [bind_ok]
  dsimp! only
  congr 3
  funext later replacement
  cases replacement <;> cases later <;> rfl

theorem next_some_at {T U : Type} (left : Slice T) (right : Slice U) (position : Nat)
    (leftBound : position < left.length) (rightBound : position < right.length) :
    bulksketch.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT T)
      (core.iter.traits.iterator.IteratorSliceIter U) (stateAt left right position) =
      Result.ok (some (left[position], right[position]), stateAt left right (position + 1),
        fun later replacement => match replacement with
          | none => later
          | some value => replaceLeft later position value.1) :=
  next_some (stateAt left right position) leftBound rightBound

theorem next_done {T U : Type} (state : State T U)
    (exhausted : state.fst.slice.length ≤ state.fst.i ∨ state.snd.slice.length ≤ state.snd.i) :
    bulksketch.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT T)
      (core.iter.traits.iterator.IteratorSliceIter U) state =
      Result.ok (none, state, fun later _ => later) := by
  have stopped : ¬ (state.fst.i < state.fst.slice.length ∧ state.snd.i < state.snd.slice.length) := by
    omega
  simp only [bulksketch.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
    Aeneas.Std.MutableZip.next, ite_eq_right stopped]

theorem next_done_at {T U : Type} (left : Slice T) (right : Slice U) (position : Nat)
    (exhausted : left.length ≤ position ∨ right.length ≤ position) :
    bulksketch.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT T)
      (core.iter.traits.iterator.IteratorSliceIter U) (stateAt left right position) =
      Result.ok (none, stateAt left right position, fun later _ => later) :=
  next_done (stateAt left right position) exhausted

theorem construct_preserves_failure {T U Input : Type}
    (right : core.iter.traits.collect.IntoIterator Input U (core.slice.iter.Iter U))
    (left : core.slice.iter.IterMut T) (input : Input) (error : Error)
    (failure : right.into_iter input = Result.fail error) :
    Aeneas.Std.MutableZip.construct right left input = Result.fail error := by
  unfold Aeneas.Std.MutableZip.construct
  rw [failure]
  exact bind_fail error _

theorem next_preserves_left_failure {T U : Type} (left : Aeneas.Std.MutableZip.LeftNext T)
    (right : core.iter.traits.iterator.Iterator (core.slice.iter.Iter U) U)
    (state : State T U) (error : Error)
    (active : state.fst.i < state.fst.slice.length ∧ state.snd.i < state.snd.slice.length)
    (failure : left state.fst = Result.fail error) :
    Aeneas.Std.MutableZip.next left right state = Result.fail error := by
  rw [Aeneas.Std.MutableZip.next, ite_eq_left active, failure]
  exact bind_fail error _

theorem next_preserves_right_failure {T U : Type} (left : Aeneas.Std.MutableZip.LeftNext T)
    (right : core.iter.traits.iterator.Iterator (core.slice.iter.Iter U) U)
    (state : State T U) (error : Error)
    (active : state.fst.i < state.fst.slice.length ∧ state.snd.i < state.snd.slice.length)
    (item : T) (advanced : core.slice.iter.IterMut T)
    (restore : core.slice.iter.IterMut T → Option T → core.slice.iter.IterMut T)
    (leftNormal : left state.fst = Result.ok (some item, advanced, restore))
    (failure : right.next state.snd = Result.fail error) :
    Aeneas.Std.MutableZip.next left right state = Result.fail error := by
  rw [Aeneas.Std.MutableZip.next, ite_eq_left active, leftNormal, bind_ok, failure]
  exact bind_fail error _

@[simp] theorem replaceLeft_length {T U : Type} (state : State T U) (position : Nat) (value : T) :
    (replaceLeft state position value).fst.slice.length = state.fst.slice.length := by
  exact Slice.setAtNat_length _ _ _

@[simp] theorem replaceLeft_left_cursor {T U : Type} (state : State T U)
    (position : Nat) (value : T) :
    (replaceLeft state position value).fst.i = state.fst.i := rfl

@[simp] theorem replaceLeft_right {T U : Type} (state : State T U) (position : Nat) (value : T) :
    (replaceLeft state position value).snd = state.snd := rfl

theorem replaceLeft_here {T U : Type} [Inhabited T] (state : State T U) (position : Nat)
    (value : T) (bounded : position < state.fst.slice.length) :
    (replaceLeft state position value).fst.slice[position]! = value := by
  rw [Slice.getElem!_Nat_eq]
  exact Slice.getElem!_Nat_setAtNat_eq _ _ _ bounded

theorem replaceLeft_elsewhere {T U : Type} [Inhabited T] (state : State T U)
    (position index : Nat) (value : T) (distinct : position ≠ index) :
    (replaceLeft state position value).fst.slice[index]! = state.fst.slice[index]! := by
  simp only [Slice.getElem!_Nat_eq]
  exact Slice.getElem!_Nat_setAtNat_ne _ _ _ _ distinct

/-- Incrementing either virtual cursor on a successful step fits in usize. -/
theorem active_cursors_fit {T U : Type} (state : State T U)
    (leftBound : state.fst.i < state.fst.slice.length)
    (rightBound : state.snd.i < state.snd.slice.length) :
    state.fst.i + 1 ≤ Usize.max ∧ state.snd.i + 1 ≤ Usize.max := by
  have leftFits : state.fst.slice.length ≤ Usize.max := state.fst.slice.length_ineq
  have rightFits : state.snd.slice.length ≤ Usize.max := state.snd.slice.length_ineq
  omega

end BulksketchBridge.MutableZip
