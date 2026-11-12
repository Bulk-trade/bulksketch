import BulksketchBridge.AffineSolveMapPivots
import BulksketchBridge.AffineSubspaces

namespace BulksketchBridge.AffineSolveMap

open Aeneas Aeneas.Std Result ControlFlow
open bulksketch.decode.affine
open FrobeniusTables (entry read_normal update_normal usize_succ)
open AffineSubspaces (iteratorAt)

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

structure EliminationState where
  kernel : Columns
  images : Columns
  preimages : Columns
  rank : Usize

def EliminationState.result (state : EliminationState) : Columns × Columns × Columns × Usize :=
  (state.kernel, state.images, state.preimages, state.rank)

def basisBit (index : Nat) : U64 := ⟨(1 : BitVec 64) <<< index⟩

private theorem basis_shift (index : Usize) (bounded : index.val < 64) :
    (1#u64 <<< index : Result U64) = .ok (basisBit index.val) := by
  obtain ⟨result, normal, _, bits⟩ := RawMulTable.normal_of_spec _ _
    (U64.ShiftLeft_spec (1#u64) index bounded)
  have equal : result = basisBit index.val := by
    apply U64.bv_eq_imp_eq
    simpa only [basisBit, U64.ofNat_bv, UScalarTy.U64_numBits_eq,
      BitVec.ofNat_eq_ofNat] using bits
  exact normal.trans (congrArg Result.ok equal)

theorem next_column (columns : Slice U64) (index : Usize)
    (active : index.val < columns.length) (small : index.val < 64) :
    ∃ next, next.val = index.val + 1 ∧
      core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter U64) (iteratorAt columns index) =
        .ok (some (index, columns[index.val]!), iteratorAt columns next) := by
  obtain ⟨next, added, nextValue⟩ := usize_succ index (by omega)
  have step : index.val < (Slice.len columns).val := by rwa [Slice.len_val]
  have inner : core.slice.iter.IteratorSliceIter.next ⟨columns, index.val⟩ =
      Result.ok (some columns[index.val]!, ⟨columns, index.val + 1⟩) := by
    simp only [core.slice.iter.IteratorSliceIter.next, step, _root_.dite_true]
    exact congrArg (fun item => Result.ok (some item, (⟨columns, index.val + 1⟩ : core.slice.iter.Iter U64)))
      (Slice.Inhabited_getElem_eq_getElem! columns index.val active)
  refine ⟨next, nextValue, ?_⟩
  simp only [core.iter.adapters.enumerate.IteratorEnumerate.next, iteratorAt, inner, bind_ok, added, nextValue]
  rfl

theorem no_column (columns : Slice U64) (index : Usize)
    (finished : columns.length ≤ index.val) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter U64) (iteratorAt columns index) =
        .ok (none, iteratorAt columns index) := by
  have inactive : ¬ index.val < (Slice.len columns).val := by rw [Slice.len_val]; omega
  have inner : core.slice.iter.IteratorSliceIter.next (⟨columns, index.val⟩ : core.slice.iter.Iter U64) =
      Result.ok (none, ⟨columns, index.val⟩) := by
    simp only [core.slice.iter.IteratorSliceIter.next, inactive, _root_.dite_false]
  simp only [core.iter.adapters.enumerate.IteratorEnumerate.next, iteratorAt, inner, bind_ok]
  rfl

/-- Records each source column's exact write to the image/preimage slots or
to the next kernel slot. The branch witness is the native pivot path. -/
inductive ColumnTrace (columns : Slice U64) :
    Nat → EliminationState → Nat → EliminationState → Prop
  | finished (index : Nat) (state : EliminationState) :
      ColumnTrace columns index state index state
  | dependent (index : Nat) (state : EliminationState) (reduced : U64) (rank : Usize)
      (path : Reduced state.images state.preimages (basisBit index) columns[index]!
        reduced 0#u64) (incr : rank.val = state.rank.val + 1)
      (endIndex : Nat) (output : EliminationState)
      (rest : ColumnTrace columns (index + 1)
        { state with kernel := state.kernel.set state.rank reduced, rank := rank } endIndex output) :
      ColumnTrace columns index state endIndex output
  | independent (index : Nat) (state : EliminationState) (reduced final : U64)
      (path : Reduced state.images state.preimages (basisBit index) columns[index]! reduced final)
      (present : final ≠ 0#u64) (endIndex : Nat) (output : EliminationState)
      (rest : ColumnTrace columns (index + 1)
        { state with
          images := inserted state.images final final
          preimages := inserted state.preimages final reduced } endIndex output) :
      ColumnTrace columns index state endIndex output

theorem eliminate_columns (columns : Slice U64) (index : Usize) (state : EliminationState)
    (width : columns.length ≤ 64) (remaining : index.val ≤ columns.length)
    (rankBound : state.rank.val ≤ index.val) (valid : Pivots state.images) :
    ∃ output : EliminationState,
      solve_map_loop1 (iteratorAt columns index) state.kernel state.images state.preimages state.rank =
        .ok output.result ∧
      ColumnTrace columns index.val state columns.length output ∧
      output.rank.val ≤ columns.length ∧ Pivots output.images := by
  suffices ∀ (fuel : Nat) (index : Usize) (state : EliminationState), index.val ≤ columns.length → columns.length - index.val = fuel →
      state.rank.val ≤ index.val → Pivots state.images →
      ∃ output : EliminationState,
        solve_map_loop1 (iteratorAt columns index) state.kernel state.images state.preimages state.rank =
          .ok output.result ∧
        ColumnTrace columns index.val state columns.length output ∧
        output.rank.val ≤ columns.length ∧ Pivots output.images by
    exact this (columns.length - index.val) index state remaining rfl rankBound valid
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro index state bounded exactFuel rankBound valid
    by_cases active : index.val < columns.length
    · have small : index.val < 64 := by omega
      obtain ⟨next, nextValue, forward⟩ := next_column columns index active small
      have normal := basis_shift index small
      obtain ⟨reduced, final, elimination, path, preserve⟩ :=
        eliminate_column state.images state.preimages (basisBit index.val) columns[index.val]! valid
      have smaller : columns.length - next.val < fuel := by omega
      have nextBound : next.val ≤ columns.length := by omega
      by_cases dependent : final = 0#u64
      · subst final
        obtain ⟨rank, added, rankValue⟩ := usize_succ state.rank (by omega)
        have slot : state.rank.val < (64#usize).val := by
          change state.rank.val < 64
          omega
        let updated : EliminationState := { state with kernel := state.kernel.set state.rank reduced, rank := rank }
        have updatedBound : updated.rank.val ≤ next.val := by change rank.val ≤ next.val; omega
        obtain ⟨output, loopEq, rest, outputBound, outputValid⟩ :=
          ih _ smaller next updated nextBound rfl updatedBound valid
        rw [nextValue] at rest
        refine ⟨output, ?_, .dependent _ _ _ _ path rankValue _ _ rest, outputBound, outputValid⟩
        have step :
            solve_map_loop1.body (iteratorAt columns index) state.kernel state.images state.preimages state.rank =
              .ok (.cont (iteratorAt columns next, updated.kernel, updated.images, updated.preimages, updated.rank)) := by
          simp only [solve_map_loop1.body, forward, bind_ok]
          dsimp! only
          simp only [normal, bind_ok, elimination, inserted, ite_true, added, updated]
          dsimp! only
          simp only [ite_true, update_normal state.kernel state.rank reduced slot, bind_ok]
        rw [solve_map_loop1, loop]
        dsimp only
        rw [step]
        simpa only [bind_ok, solve_map_loop1] using loopEq
      · let updated : EliminationState := { state with
          images := inserted state.images final final
          preimages := inserted state.preimages final reduced }
        have updatedBound : updated.rank.val ≤ next.val := by change state.rank.val ≤ next.val; omega
        obtain ⟨output, loopEq, rest, outputBound, outputValid⟩ :=
          ih _ smaller next updated nextBound rfl updatedBound preserve
        rw [nextValue] at rest
        refine ⟨output, ?_, .independent _ _ _ _ path dependent _ _ rest, outputBound, outputValid⟩
        have step :
            solve_map_loop1.body (iteratorAt columns index) state.kernel state.images state.preimages state.rank =
              .ok (.cont (iteratorAt columns next, updated.kernel, updated.images, updated.preimages, updated.rank)) := by
          simp only [solve_map_loop1.body, forward, bind_ok]
          dsimp! only
          simp only [normal, bind_ok, elimination, updated]
          dsimp! only
          simp only [dependent, ite_false]
        rw [solve_map_loop1, loop]
        dsimp only
        rw [step]
        simpa only [bind_ok, solve_map_loop1] using loopEq
    · have atEnd : index.val = columns.length := by omega
      have trace : ColumnTrace columns index.val state columns.length state :=
        atEnd ▸ ColumnTrace.finished index.val state
      refine ⟨state, ?_, trace, by omega, valid⟩
      rw [solve_map_loop1, loop]
      simp only [solve_map_loop1.body, no_column columns index (by omega), bind_ok]
      dsimp! only
      simp only [bind_ok, EliminationState.result]

#print axioms eliminate_columns

end BulksketchBridge.AffineSolveMap
