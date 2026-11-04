import BulksketchBridge.RawMulAccumSpec
import BulksketchProofs.Field.CLMul

/-!
Refinement of the unchanged second native multiplication loop. The proof uses
the concrete Aeneas range/StepBy model; its Rust-library correspondence remains
part of the recorded extraction/runtime trusted boundary.
-/

namespace BulksketchBridge.RawMulAccum

open Aeneas Aeneas.Std

private theorem eq_ok_of_spec {α : Type} (program : Result α) (expected : α)
    (h : program ⦃ output => output = expected ⦄) : program = Result.ok expected := by
  cases program using Result.cases <;> simp_all

private theorem start_val (count : Nat) (h : count ≤ 16) :
    (iteratorAt count).iter.start.val = 4 * count := by
  change (4 * count) % 2 ^ 32 = 4 * count
  apply Nat.mod_eq_of_lt
  omega

private theorem iterator_eq (it : Iterator) (count : Nat) (h : count ≤ 16)
    (hs : it.iter.start.val = 4 * count)
    (he : it.iter.end = 64#u32) (hp : it.step_by = 4#usize) :
    it = iteratorAt count := by
  have hs' : it.iter.start = (iteratorAt count).iter.start :=
    UScalar.eq_of_val_eq (hs.trans (start_val count h).symm)
  cases it with
  | mk iter step =>
    cases iter
    simp_all [iteratorAt]

private theorem iterator_next (count : Nat) (h : count < 16) :
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepU32)
      (iteratorAt count) =
      Result.ok (some (iteratorAt count).iter.start, iteratorAt (count + 1)) := by
  apply eq_ok_of_spec
  apply WP.spec_mono
    (core.iter.adapters.step_by.IteratorStepBy.next_Range_U32_some_spec
      (iteratorAt count) ?_ ?_ ?_)
  · intro result hr
    rcases result with ⟨opt, it⟩
    rcases hr with ⟨ho, hs, he, hp⟩
    have hit : it = iteratorAt (count + 1) := by
      apply iterator_eq it (count + 1) (by omega)
      · have hstep : (iteratorAt count).step_by.val = 4 := by simp [iteratorAt]
        rw [start_val count (by omega), hstep] at hs
        omega
      · exact he
      · exact hp
    simp_all
  · simp only [start_val count (by omega)]
    change 4 * count < 64
    omega
  · change 0 < (4#usize).val
    simp
  · simp only [start_val count (by omega)]
    change 4 * count + 4 ≤ 64
    omega

private theorem iterator_terminal :
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepU32)
      (iteratorAt 16) = Result.ok (none, iteratorAt 16) := by
  apply eq_ok_of_spec
  apply WP.spec_mono
    (core.iter.adapters.step_by.IteratorStepBy.next_Range_U32_none_spec
      (iteratorAt 16) (by decide))
  intro result hr
  rcases result with ⟨opt, it⟩
  rcases hr with ⟨ho, hi⟩
  simp_all

/-- The source's mask, pointer-width cast, and both shifts are lossless and safe. -/
theorem nibble_bounds : NibbleBounds := by
  intro right count hc
  have hn : (nibbleWord right count).val < 16 := by
    change ((right.bv >>> (4 * count)) &&& (15 : BitVec 64)).toNat < 16
    rw [BitVec.toNat_and]
    change (right.bv >>> (4 * count)).toNat &&& 15 < 16
    have h := Nat.and_le_right (n := (right.bv >>> (4 * count)).toNat)
      (m := (15 : BitVec 64).toNat)
    change (right.bv >>> (4 * count)).toNat &&& 15 ≤ 15 at h
    omega
  have hcast : (UScalar.cast .Usize (nibbleWord right count)).val =
      (nibbleWord right count).val := by
    rw [UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    cases System.Platform.numBits_eq with
    | inl h => simp [UScalarTy.numBits, h]; omega
    | inr h => simp [UScalarTy.numBits, h]; omega
  refine ⟨by omega, by omega, by omega, hcast, ?_⟩
  rw [hcast]
  change BitVec.ofNat 4
    (((right.bv >>> (4 * count)) &&& (15 : BitVec 64)).toNat) = _
  rw [BitVec.ofNat_toNat, BitVec.setWidth_and]
  change _ &&& BitVec.allOnes 4 = _
  exact BitVec.and_allOnes

private theorem right_shift (right : U64) (count : Nat) (hc : count < 16) :
    right >>> (iteratorAt count).iter.start =
      Result.ok (⟨right.bv >>> (4 * count)⟩ : U64) := by
  change UScalar.shiftRight right (iteratorAt count).iter.start.val = _
  rw [start_val count (by omega)]
  simp only [UScalar.shiftRight]
  rw [ite_eq_left (show 4 * count < UScalarTy.U64.numBits by change 4 * count < 64; omega)]
  rfl

private theorem left_shift (word : U128) (count : Nat) (hc : count < 16) :
    word <<< (iteratorAt count).iter.start =
      Result.ok (⟨word.bv <<< (4 * count)⟩ : U128) := by
  change UScalar.shiftLeft word (iteratorAt count).iter.start.val = _
  rw [start_val count (by omega)]
  simp only [UScalar.shiftLeft]
  rw [ite_eq_left (show 4 * count < UScalarTy.U128.numBits by change 4 * count < 128; omega)]
  rfl

private theorem table_lookup (left right : U64) (table : RawMulTable.Table)
    (ht : RawMulTable.TableCorrect left table) (count : Nat) (hc : count < 16) :
    Array.index_usize table (UScalar.cast .Usize (nibbleWord right count)) =
      Result.ok (⟨BulksketchProofs.Field.nibbleMultiple left.bv
        ((right.bv >>> (4 * count)).setWidth 4)⟩ : U128) := by
  have hb := nibble_bounds right count hc
  have hentry := ht (UScalar.cast .Usize (nibbleWord right count)).val hb.2.2.1
  rw [hb.2.2.2.2] at hentry
  simp only [Array.index_usize, Array.getElem?_Usize_eq, hentry]

/-- Every generated accumulation step implements the next four polynomial bits. -/
theorem body_step : BodyStep := by
  intro left right table ht count hc
  simp only [bulksketch.field.gf64.raw_mul_loop1.body, iterator_next count hc,
    bind_ok]
  change (do
    let i ← right >>> (iteratorAt count).iter.start
    let i1 ← lift (i &&& 15#u64)
    let i2 ← lift (UScalar.cast .Usize i1)
    let i3 ← Array.index_usize table i2
    let i4 ← i3 <<< (iteratorAt count).iter.start
    let product1 ← lift (prefixWord left right count ^^^ i4)
    Result.ok (ControlFlow.cont (iteratorAt (count + 1), product1))) = _
  rw [right_shift right count hc]
  simp only [Bind.bind, lift, bind_ok]
  change (do
    let i3 ← Array.index_usize table (UScalar.cast .Usize (nibbleWord right count))
    let i4 ← i3 <<< (iteratorAt count).iter.start
    Result.ok (ControlFlow.cont (iteratorAt (count + 1),
      (prefixWord left right count) ^^^ i4))) = _
  rw [table_lookup left right table ht count hc]
  simp only [Bind.bind, bind_ok, left_shift _ count hc]
  congr 3
  apply congrArg (fun word : BitVec 128 => (⟨word⟩ : U128))
  exact (BulksketchProofs.Field.clmulPrefix_nibble_step left.bv right.bv count).symm

/-- At the final source iterator state the body exits before shifting. -/
theorem terminal_body : TerminalBody := by
  intro left right table
  simp only [bulksketch.field.gf64.raw_mul_loop1.body, iterator_terminal, bind_ok]
  rfl

/-- Every valid original loop suffix terminates with the full polynomial product. -/
theorem every_prefix_completes : EveryPrefixCompletes := by
  intro left right table ht count hc
  suffices ∀ remaining count, count ≤ 16 → 16 - count = remaining →
      bulksketch.field.gf64.raw_mul_loop1 (iteratorAt count) right table
        (prefixWord left right count) = Result.ok (outputWord left right) from
    this (16 - count) count hc rfl
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro count hc he
    by_cases hend : count = 16
    · subst count
      unfold bulksketch.field.gf64.raw_mul_loop1
      unfold loop
      simp only [terminal_body left right table, bind_ok]
    · have hlt : count < 16 := by omega
      have hrec := ih (16 - (count + 1)) (by omega) (count + 1) (by omega) rfl
      unfold bulksketch.field.gf64.raw_mul_loop1
      unfold loop
      simp only [body_step left right table ht count hlt, bind_ok]
      exact hrec

end BulksketchBridge.RawMulAccum
