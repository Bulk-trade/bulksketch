import BulksketchBridge.RawMulTableSpec
import BulksketchBridge.RawMulTableChallenges
import BulksketchProofs.Field.NibbleTable

/-!
# First actual raw-multiplication loop: full table and total correctness

The generated loop/body are imported unchanged. The invariant permits arbitrary
unused tail values; all reads, subtraction and shifts are justified before the
original array update. No successful source result is assumed.
-/

namespace BulksketchBridge.RawMulTable

open Aeneas Aeneas.Std Aeneas.Std.WP

private theorem usize_one_val : (1#usize).val = 1 := by simp
private theorem usize_sixteen_val : (16#usize).val = 16 := by simp

/-- Total-WP correctness of a Result computation exposes an actual normal result. -/
theorem normal_of_spec {α : Type} (computation : Result α) (post : α → Prop)
    (h : computation ⦃ post ⦄) : ∃ value, computation = Result.ok value ∧ post value := by
  cases computation using Result.cases with
  | ret value => exact ⟨value, rfl, (spec_ok value).mp h⟩
  | vis effect continuation => exact False.elim ((spec_vis effect continuation).mp h)
  | div => exact False.elim ((spec_div).mp h)

/-- The source's cleared-bit address is earlier than the current initialized entry. -/
theorem cleared_index_bounds (index previous : Usize)
    (positive : 1 ≤ index.val) (small : index.val < 16)
    (previousEq : previous.val = index.val - 1) :
    (index &&& previous).val < index.val ∧ (index &&& previous).val < 16 := by
  simp only [UScalar.val_and, previousEq]
  have bounds := BulksketchProofs.Field.nibble_low_bit_bounds index.val (by omega) small
  exact ⟨bounds.1, bounds.2.1⟩

/-- Prefix correctness supplies the exact source indexed read, not just reduced equality. -/
theorem prefix_index_normal (left : U64) (table : Table) (count : Nat) (index : Usize)
    (prefixCorrect : TablePrefixCorrect left table count) (earlier : index.val < count) :
    Array.index_usize table index =
      Result.ok (⟨BulksketchProofs.Field.nibbleMultiple left.bv
        (BitVec.ofNat 4 index.val)⟩ : U128) := by
  simp only [Array.index_usize, Array.getElem?_Usize_eq, prefixCorrect index.val earlier]

/-- A source write at the next index extends the exact initialized prefix by one. -/
theorem prefix_after_set (left : U64) (table : Table) (index : Usize)
    (prefixCorrect : TablePrefixCorrect left table index.val) (small : index.val < 16) :
    TablePrefixCorrect left
      (table.set index (⟨BulksketchProofs.Field.nibbleMultiple left.bv
        (BitVec.ofNat 4 index.val)⟩ : U128)) (index.val + 1) := by
  intro slot before
  rw [Array.set_val_eq]
  by_cases same : index.val = slot
  · subst slot
    apply List.getElem?_set_self
    simpa only [Array.property, usize_sixteen_val] using small
  · rw [List.getElem?_set_ne same]
    exact prefixCorrect slot (by omega)

/-- The real initial zero array establishes exactly the consumed prefix at index one. -/
theorem initial_prefix (left : U64) :
    TablePrefixCorrect left (Array.repeat 16#usize 0#u128) 1 := by
  intro index below
  have indexEq : index = 0 := by omega
  subst index
  simp [Array.repeat_val]
  apply U128.bv_eq_imp_eq
  exact (BulksketchProofs.Field.nibbleMultiple_zero left.bv).symm

/-- Every actual source body either finishes or preserves the invariant with a
strictly smaller remaining iteration count. -/
theorem body_preserves_prefix (left : U64)
    (state : core.ops.range.Range Usize × Table)
    (invariant : LoopInvariant left state) :
    bulksketch.field.gf64.raw_mul_loop0.body left state.1 state.2 ⦃ result =>
      match result with
      | .done final => TableCorrect left final
      | .cont next => LoopInvariant left next ∧
          16 - next.1.start.val < 16 - state.1.start.val ⦄ := by
  rcases state with ⟨range, table⟩
  simp only [LoopInvariant] at invariant
  rcases invariant with ⟨endEq, positive, atMost16, prefixCorrect⟩
  by_cases active : range.start.val < 16
  · have rangeActive : range.start.val < range.«end».val := by
      rw [endEq, usize_sixteen_val]
      exact active
    obtain ⟨⟨option, advanced⟩, nextNormal, nextPost⟩ := normal_of_spec _ _
      (core.iter.range.IteratorRange.next_Usize_some_spec range rangeActive)
    rcases nextPost with ⟨rfl, advanceEq, advanceEnd⟩
    obtain ⟨previous, subtractNormal, previousEq, _⟩ := normal_of_spec _ _
      (Usize.sub_spec (x := range.start) (y := 1#usize)
        (by simpa only [usize_one_val] using positive))
    rw [usize_one_val] at previousEq
    let cleared := range.start &&& previous
    have clearedEq : cleared.val = range.start.val &&& (range.start.val - 1) := by
      simp only [cleared, UScalar.val_and, previousEq]
    have earlier := cleared_index_bounds range.start previous positive active previousEq
    have indexNormal := prefix_index_normal left table range.start.val cleared prefixCorrect earlier.1
    obtain ⟨count, countNormal, countEq, countSmall⟩ :=
      usize_trailing_zeros_nibble range.start positive active
    obtain ⟨shifted, shiftNormal, _, shiftBits⟩ := normal_of_spec _ _
      (U128.ShiftLeft_spec (core.convert.num.FromU128U64.from left) count (by omega))
    have shiftedEq : shifted = (⟨left.bv.setWidth 128 <<< count.val⟩ : U128) := by
      apply U128.bv_eq_imp_eq
      exact shiftBits
    have valueEq :
        (⟨BulksketchProofs.Field.nibbleMultiple left.bv
          (BitVec.ofNat 4 cleared.val)⟩ : U128) ^^^ shifted =
        (⟨BulksketchProofs.Field.nibbleMultiple left.bv
          (BitVec.ofNat 4 range.start.val)⟩ : U128) := by
      rw [shiftedEq]
      apply congrArg (fun bits : BitVec 128 => (⟨bits⟩ : U128))
      rw [countEq, clearedEq]
      exact (BulksketchProofs.Field.nibble_clear_low_bit left.bv range.start.val (by omega) active).symm
    have writeBound : range.start.val < table.length := by
      simpa only [Array.property, usize_sixteen_val] using active
    obtain ⟨updated, updateNormal, updatedEq⟩ := normal_of_spec _ _
      (Array.update_spec table range.start
        (⟨BulksketchProofs.Field.nibbleMultiple left.bv
          (BitVec.ofNat 4 range.start.val)⟩ : U128) writeBound)
    dsimp only [cleared] at indexNormal valueEq
    have bodyNormal : bulksketch.field.gf64.raw_mul_loop0.body left range table =
        Result.ok (ControlFlow.cont (advanced, updated)) := by
      simp only [bulksketch.field.gf64.raw_mul_loop0.body, nextNormal, bind_ok]
      change (do
        let previous ← range.start - 1#usize
        let address ← lift (range.start &&& previous)
        let entry ← Array.index_usize table address
        let widened ← lift (core.convert.num.FromU128U64.from left)
        let count ← core.num.Usize.trailing_zeros range.start
        let shifted ← widened <<< count
        let value ← lift (entry ^^^ shifted)
        let updated ← Array.update table range.start value
        Result.ok (ControlFlow.cont (advanced, updated))) = _
      rw [subtractNormal]
      simp only [Bind.bind, lift, bind_ok, indexNormal, countNormal, shiftNormal,
        valueEq, updateNormal]
    rw [bodyNormal]
    apply (spec_ok _).mpr
    change LoopInvariant left (advanced, updated) ∧
      16 - advanced.start.val < 16 - range.start.val
    simp only [LoopInvariant]
    constructor
    · refine ⟨advanceEnd.trans endEq, ?_, ?_, ?_⟩
      · omega
      · omega
      · rw [advanceEq, updatedEq]
        exact prefix_after_set left table range.start prefixCorrect active
    · omega
  · have atEnd : range.start.val = 16 := by omega
    have rangeDone : range.start.val ≥ range.«end».val := by
      rw [endEq, usize_sixteen_val]
      omega
    obtain ⟨⟨option, unchanged⟩, nextNormal, nextPost⟩ := normal_of_spec _ _
      (core.iter.range.IteratorRange.next_Usize_none_spec range rangeDone)
    rcases nextPost with ⟨optionEq, _⟩
    rw [optionEq] at nextNormal
    simp only [bulksketch.field.gf64.raw_mul_loop0.body, nextNormal, bind_ok]
    change Result.ok (ControlFlow.done table) ⦃ result =>
      match result with
      | .done final => TableCorrect left final
      | .cont next => LoopInvariant left next ∧
          16 - next.1.start.val < 16 - range.start.val ⦄
    rw [spec_ok]
    simpa only [TableCorrect, atEnd] using prefixCorrect

/-- Every bounded source-loop suffix completes normally with all sixteen exact entries. -/
theorem every_initialized_prefix_completes :
    BulksketchBridge.RawMulTableChallenges.everyInitializedPrefixCompletes := by
  intro left range table invariant
  have complete : bulksketch.field.gf64.raw_mul_loop0 range left table ⦃ TableCorrect left ⦄ := by
    unfold bulksketch.field.gf64.raw_mul_loop0
    exact loop.spec_decr_nat
      (fun state : core.ops.range.Range Usize × Table => 16 - state.1.start.val)
      (LoopInvariant left) (TableCorrect left)
      (fun (range, table) => bulksketch.field.gf64.raw_mul_loop0.body left range table)
      (range, table) (by
        intro state invariant
        rcases state with ⟨range, table⟩
        dsimp only
        apply WP.spec_mono (body_preserves_prefix left (range, table) invariant)
        intro result post
        cases result with
        | done final => exact post
        | cont next => exact post) invariant
  exact normal_of_spec _ _ complete

/-- The real source initialization and first loop produce the complete128-bit nibble table. -/
theorem initialized_table_loop_completes :
    BulksketchBridge.RawMulTableChallenges.initializedTableLoopCompletes := by
  intro left
  apply every_initialized_prefix_completes left
    { start := 1#usize, «end» := 16#usize } (Array.repeat 16#usize 0#u128)
  exact ⟨rfl, by decide, by decide, initial_prefix left⟩

end BulksketchBridge.RawMulTable
