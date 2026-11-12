import Arithmetic.DenseSquareGenerated
import BulksketchBridge.Square

namespace BulksketchBridge.DenseSquare

open Aeneas Aeneas.Std
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial

abbrev State := Aeneas.Std.DenseSquareRuntime.State U64 U64

def stateAt (left right : Slice U64) (i : Nat) : State :=
  ⟨⟨⟨left, 2 * i⟩, 2#usize⟩, ⟨right, i⟩⟩

def replace (state : State) (i : Nat) (value : U64) : State :=
  ⟨{ state.fst with iter := { state.fst.iter with
      slice := state.fst.iter.slice.setAtNat (2 * i) value } }, state.snd⟩

private theorem mutable_slice_next (iterator : core.slice.iter.IterMut U64)
    (bounded : iterator.i < iterator.slice.length) :
    core.slice.iter.IteratorIterMut.next iterator =
      Result.ok (some iterator.slice[iterator.i]!, { iterator with i := iterator.i + 1 },
        fun later replacement => match replacement with
          | none => later
          | some value => { later with slice := later.slice.setAtNat iterator.i value }) := by
  have lengthGuard : iterator.i < iterator.slice.len.val := by simpa using bounded
  have step : core.slice.iter.IteratorIterMut.next iterator =
      Result.ok (some (iterator.slice[iterator.i]'bounded), { iterator with i := iterator.i + 1 },
        fun later replacement => match replacement with
          | none => later
          | some value => { later with slice := later.slice.setAtNat iterator.i value }) := by
    unfold core.slice.iter.IteratorIterMut.next
    split
    · dsimp only
      congr 3
      funext later replacement
      cases replacement <;> rfl
    · contradiction
  rw [step, Slice.Inhabited_getElem_eq_getElem! iterator.slice iterator.i bounded]

private theorem next_some (left right : Slice U64) (i : Nat)
    (lengthEq : left.length = 2 * right.length) (active : i < right.length) :
    DenseSquareRuntime.next (DenseSquareRuntime.stepNext (DenseSquareRuntime.leftNext U64))
      (core.iter.traits.iterator.IteratorSliceIter U64) (stateAt left right i) =
      Result.ok (some (left[2 * i]!, right[i]!), stateAt left right (i + 1),
        fun later replacement => match replacement with
          | none => later
          | some value => replace later i value.1) := by
  have leftBound : 2 * i < left.length := by omega
  have rightLen : i < right.len.val := by simpa using active
  have leftStep : core.slice.iter.IteratorIterMut.next (⟨left, 2 * i⟩ : core.slice.iter.IterMut U64) =
      Result.ok (some left[2 * i]!, ⟨left, 2 * i + 1⟩, fun later replacement =>
        match replacement with
        | none => later
        | some value => { later with slice := later.slice.setAtNat (2 * i) value }) :=
    mutable_slice_next ⟨left, 2 * i⟩ leftBound
  have rightStep : core.slice.iter.IteratorSliceIter.next (⟨right, i⟩ : core.slice.iter.Iter U64) =
      Result.ok (some right[i]!, ⟨right, i + 1⟩) := by
    have step : core.slice.iter.IteratorSliceIter.next (⟨right, i⟩ : core.slice.iter.Iter U64) =
        Result.ok (some (right[i]'active), ⟨right, i + 1⟩) := by
      unfold core.slice.iter.IteratorSliceIter.next
      split
      · rfl
      · contradiction
    rw [step, Slice.Inhabited_getElem_eq_getElem! right i active]
  have advance : min left.length (2 * i + (2#usize).val) = 2 * (i + 1) := by
    rw [show (2#usize).val = 2 by simp, min_eq_right (by omega)]
    omega
  have strideStep : DenseSquareRuntime.stepNext (DenseSquareRuntime.leftNext U64)
      (stateAt left right i).fst =
      Result.ok (some left[2 * i]!, (stateAt left right (i + 1)).fst,
        fun later replacement => { later with iter := match replacement with
          | none => later.iter
          | some value => { later.iter with slice := later.iter.slice.setAtNat (2 * i) value } }) := by
    simp only [DenseSquareRuntime.stepNext, DenseSquareRuntime.leftNext, stateAt, leftStep, bind_ok]
    dsimp! only
    rw [advance]
  rw [DenseSquareRuntime.next, strideStep, bind_ok]
  rw [show (core.iter.traits.iterator.IteratorSliceIter U64).next (stateAt left right i).snd = _ from rightStep]
  simp only [bind_ok]
  dsimp! only
  congr 3
  funext later replacement
  cases replacement <;> cases later <;> rfl

private theorem next_done (left right : Slice U64) (lengthEq : left.length = 2 * right.length) :
    DenseSquareRuntime.next (DenseSquareRuntime.stepNext (DenseSquareRuntime.leftNext U64))
      (core.iter.traits.iterator.IteratorSliceIter U64) (stateAt left right right.length) =
      Result.ok (none, stateAt left right right.length, fun later _ => later) := by
  have inactive : ¬ (2 * right.length < left.len.val) := by simp [lengthEq]
  have leftDone : core.slice.iter.IteratorIterMut.next (stateAt left right right.length).fst.iter =
      Result.ok (none, (stateAt left right right.length).fst.iter, fun later _ => later) := by
    unfold core.slice.iter.IteratorIterMut.next
    split
    · rename_i active
      exact False.elim (inactive (by simpa [stateAt] using active))
    · rfl
  simp only [DenseSquareRuntime.next, DenseSquareRuntime.stepNext, DenseSquareRuntime.leftNext,
    leftDone, bind_ok]
  dsimp! only
  simp only [bind_ok]
  rfl

/-- Even slots from the chosen scan position are replaced. Earlier positions
and odd slots retain the corresponding original value. -/
def squareFrom (left right : Slice U64) (start : Nat) : Slice U64 :=
  Slice.from (List.ofFn fun i : Fin left.length =>
    if i.val % 2 = 0 ∧ start ≤ i.val / 2 then Square.expectedWord right[i.val / 2]!
    else left[i.val]!) (by simp)

@[simp] theorem squareFrom_length (left right : Slice U64) (start : Nat) :
    (squareFrom left right start).length = left.length := by simp [squareFrom]

theorem squareFrom_word (left right : Slice U64) (start i : Nat) (bounded : i < left.length) :
    (squareFrom left right start)[i]! =
      if i % 2 = 0 ∧ start ≤ i / 2 then Square.expectedWord right[i / 2]! else left[i]! := by
  simp only [squareFrom, Slice.getElem!_Nat_eq, Slice.from_val]
  rw [← List.Inhabited_getElem_eq_getElem! _ i (by simpa using bounded), List.getElem_ofFn]

private theorem squareFrom_done (left right : Slice U64) (lengthEq : left.length = 2 * right.length) :
    squareFrom left right right.length = left := by
  apply Slice.ext_getElem (squareFrom_length _ _ _)
  intro i mappedBound bounded
  rw [Slice.Inhabited_getElem_eq_getElem! _ i mappedBound, Slice.Inhabited_getElem_eq_getElem! left i bounded,
    squareFrom_word left right _ i bounded, ite_eq_right (by omega)]

private theorem replace_squareFrom (left right : Slice U64) (i : Nat)
    (_lengthEq : left.length = 2 * right.length) (_active : i < right.length) :
    replace (stateAt (squareFrom left right (i + 1)) right right.length) i
        (Square.expectedWord right[i]!) = stateAt (squareFrom left right i) right right.length := by
  have update : (squareFrom left right (i + 1)).setAtNat (2 * i)
      (Square.expectedWord right[i]!) = squareFrom left right i := by
    apply Slice.ext_getElem (by simp)
    intro j updatedBound outputBound
    have bounded : j < left.length := by simpa using outputBound
    rw [Slice.Inhabited_getElem_eq_getElem! _ j updatedBound,
      Slice.Inhabited_getElem_eq_getElem! _ j outputBound,
      squareFrom_word left right _ j bounded, Slice.getElem!_Nat_eq]
    by_cases same : 2 * i = j
    · subst j
      rw [Slice.getElem!_Nat_setAtNat_eq _ _ _ (by simp; omega), ite_eq_left (by omega)]
      congr 2
      omega
    · rw [Slice.getElem!_Nat_setAtNat_ne _ _ _ _ same, ← Slice.getElem!_Nat_eq,
        squareFrom_word left right _ j bounded]
      have sameGuard : (j % 2 = 0 ∧ i + 1 ≤ j / 2) ↔ (j % 2 = 0 ∧ i ≤ j / 2) := by omega
      simp only [sameGuard]
  simp only [replace, stateAt, update]

private theorem body_step {K : Type} (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (nativeSquare : ∀ input, kernels.ArithmeticInst.square input =
      bulksketch.field.gf64.square bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input)
    (left right : Slice U64) (i : Nat) (lengthEq : left.length = 2 * right.length)
    (active : i < right.length) (back : State → State) :
    square_into_loop.body bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels
      (stateAt left right i) back = Result.ok (ControlFlow.cont (stateAt left right (i + 1),
        fun later => back (replace later i (Square.expectedWord right[i]!)))) := by
  simp only [square_into_loop.body, next_some left right i lengthEq active, bind_ok]
  dsimp! only
  simp only [nativeSquare, Square.square_refines, bind_ok]

private theorem body_done {K : Type} (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (left right : Slice U64) (lengthEq : left.length = 2 * right.length) (back : State → State) :
    square_into_loop.body bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels
      (stateAt left right right.length) back =
        Result.ok (ControlFlow.done (back (stateAt left right right.length))) := by
  simp only [square_into_loop.body, next_done left right lengthEq, bind_ok]
  dsimp! only

theorem square_loop_refines {K : Type}
    (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (nativeSquare : ∀ input, kernels.ArithmeticInst.square input =
      bulksketch.field.gf64.square bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input)
    (left right : Slice U64) (lengthEq : left.length = 2 * right.length)
    (start : Nat) (bounded : start ≤ right.length) (back : State → State) :
    square_into_loop bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels
      (stateAt left right start) back =
        Result.ok (back (stateAt (squareFrom left right start) right right.length)) := by
  suffices ∀ remaining start, start ≤ right.length → right.length - start = remaining →
    ∀ back : State → State,
      square_into_loop bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels
        (stateAt left right start) back =
          Result.ok (back (stateAt (squareFrom left right start) right right.length))
    from this (right.length - start) start bounded rfl back
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro start bounded eq back
    by_cases active : start < right.length
    · have rest := ih (right.length - (start + 1)) (by omega) (start + 1) (by omega) rfl
        (fun later => back (replace later start (Square.expectedWord right[start]!)))
      unfold square_into_loop
      unfold loop
      dsimp only
      rw [body_step kernels nativeSquare left right start lengthEq active back]
      simp only [bind_ok]
      change square_into_loop bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels
        (stateAt left right (start + 1))
        (fun later => back (replace later start (Square.expectedWord right[start]!))) = _
      rw [rest]
      simp only [replace_squareFrom left right start lengthEq active]
    · have terminal : start = right.length := by omega
      subst start
      unfold square_into_loop
      unfold loop
      dsimp only
      simp only [body_done kernels left right lengthEq back, bind_ok, squareFrom_done left right lengthEq]

end BulksketchBridge.DenseSquare
