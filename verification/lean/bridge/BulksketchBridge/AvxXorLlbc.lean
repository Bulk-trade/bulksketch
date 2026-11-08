import BulksketchBridge.AvxXorLlbcGenerated

namespace BulksketchBridge.AvxXorLlbc

open Aeneas.Std Aeneas.Std.Avx512Register
open X86MaskedMemory

private theorem chunk_refines (heap : Memory) (permit : Nat → Bool)
    (left right : Llbc.SliceView) (size : left.len.val ≤ 8)
    (same : right.len.val = left.len.val) (leftWords rightWords : Nat → BitVec 64)
    (leftBytes : WordWindow heap left.base left.len.val leftWords)
    (rightBytes : WordWindow heap right.base right.len.val rightWords)
    (writable : WritableWindow heap permit left.base left.len.val) :
    ∃ updated : Memory,
      runChunk permit left right program.ops [] heap = some updated ∧
      WordWindow updated left.base left.len.val (fun index => leftWords index ^^^ rightWords index) ∧
      ∀ address, address < left.base ∨ left.base + 8 * left.len.val ≤ address →
        updated address = heap address := by
  have rightSize : right.len.val ≤ 8 := same ▸ size
  let leftLanes : Lanes := fun lane => if lane.val < left.len.val then leftWords lane.val else 0
  let rightLanes : Lanes := fun lane => if lane.val < right.len.val then rightWords lane.val else 0
  let value : Word512 := fun pair high =>
    unflatten leftLanes pair high ^^^ unflatten rightLanes pair high
  have leftRead := load_window left size heap permit leftWords leftBytes
  have rightRead := load_window right rightSize heap permit rightWords rightBytes
  change Llbc.exec permit Llbc.loadProgram (Llbc.loadInput heap left) =
    some (.register (unflatten leftLanes), heap) at leftRead
  change Llbc.exec permit Llbc.loadProgram (Llbc.loadInput heap right) =
    some (.register (unflatten rightLanes), heap) at rightRead
  obtain ⟨updated, write, bytes, frame⟩ := store_window left size heap permit value writable
  refine ⟨updated, ?_, ?_, frame⟩
  · dsimp only [value] at write
    simp [program, runChunk, leftRead, rightRead, xorWords, Result.match.ok, write]
  · intro index bounded byte
    have lane : index < 8 := by omega
    have rightBound : index < right.len.val := by omega
    have laneValue : flatten value ⟨index, lane⟩ = leftWords index ^^^ rightWords index := by
      change flatten (unflatten leftLanes) ⟨index, lane⟩ ^^^
        flatten (unflatten rightLanes) ⟨index, lane⟩ = _
      simp [leftLanes, rightLanes, bounded, rightBound]
    simpa only [dite_eq_left lane, laneValue] using bytes index bounded byte

/-- The source view lies outside the writable destination view. -/
def Separated (left right : Llbc.SliceView) : Prop :=
  ∀ offset : Nat, offset < 8 * right.len.val →
    right.base + offset < left.base ∨ left.base + 8 * left.len.val ≤ right.base + offset

private theorem run_refines (heap : Memory) (permit : Nat → Bool)
    (left right : Llbc.SliceView) (same : right.len.val = left.len.val)
    (leftWords rightWords : Nat → BitVec 64)
    (leftBytes : WordWindow heap left.base left.len.val leftWords)
    (rightBytes : WordWindow heap right.base right.len.val rightWords)
    (writable : WritableWindow heap permit left.base left.len.val)
    (separated : Separated left right) :
    ∃ updated : Memory,
      run program permit left right heap = some updated ∧
      WordWindow updated left.base left.len.val (fun index => leftWords index ^^^ rightWords index) ∧
      ∀ address, address < left.base ∨ left.base + 8 * left.len.val ≤ address →
        updated address = heap address := by
  by_cases nonempty : 0 < left.len.val
  · let n := min 8 left.len.val
    have nLe : n ≤ left.len.val := Nat.min_le_right _ _
    have nSize : n ≤ 8 := Nat.min_le_left _ _
    have splitSize : n + (left.len.val - 8) = left.len.val := by
      dsimp only [n]
      omega
    have rightN : min 8 right.len.val = n := by rw [same]
    have firstSize : (take left 8).len.val ≤ 8 := by simpa only [take_len] using nSize
    have firstSame : (take right 8).len.val = (take left 8).len.val := by simp only [take_len, same]
    have firstLeft : WordWindow heap (take left 8).base (take left 8).len.val leftWords := by
      intro i hi b
      exact leftBytes i (by simpa only [take_len] using Nat.lt_of_lt_of_le hi (show n ≤ _ from nLe)) b
    have firstRight : WordWindow heap (take right 8).base (take right 8).len.val rightWords := by
      intro i hi b
      have bound : i < n := by simpa only [take_len, rightN] using hi
      exact rightBytes i (by omega) b
    have firstWrite : WritableWindow heap permit (take left 8).base (take left 8).len.val := by
      intro off h
      simp only [take_base, take_len] at *
      apply writable
      omega
    obtain ⟨first, firstRun, firstBytes, firstFrame⟩ := chunk_refines heap permit
      (take left 8) (take right 8) firstSize firstSame leftWords rightWords firstLeft firstRight firstWrite
    simp only [take_base, take_len] at firstBytes firstFrame
    have tailSame : (drop right 8).len.val = (drop left 8).len.val := by simp only [drop_len, same]
    have tailLeft : WordWindow first (drop left 8).base (drop left 8).len.val
        (fun i => leftWords (n + i)) := by
      intro i hi b
      simp only [drop_base, drop_len] at hi ⊢
      change first (left.base + 8 * n + 8 * i + b.val) = _
      rw [firstFrame _ (Or.inr (by omega))]
      rw [show left.base + 8 * n + 8 * i + b.val = left.base + 8 * (n + i) + b.val by omega]
      exact leftBytes _ (by omega) _
    have tailRight : WordWindow first (drop right 8).base (drop right 8).len.val
        (fun i => rightWords (n + i)) := by
      intro i hi b
      simp only [drop_base, drop_len, same] at hi ⊢
      have byteBound := b.isLt
      have outside := separated (8 * n + 8 * i + b.val) (by omega)
      have address : right.base + 8 * n + 8 * i + b.val = right.base + (8 * n + 8 * i + b.val) := by omega
      rw [address, firstFrame _ (by omega)]
      rw [show right.base + (8 * n + 8 * i + b.val) = right.base + 8 * (n + i) + b.val by omega]
      exact rightBytes _ (by omega) _
    have tailWrite : WritableWindow first permit (drop left 8).base (drop left 8).len.val := by
      intro off h
      simp only [drop_base, drop_len] at h ⊢
      change (first (left.base + 8 * n + off)).isSome = true ∧ permit (left.base + 8 * n + off) = true
      rw [firstFrame _ (Or.inr (by omega)), Nat.add_assoc]
      exact writable _ (by omega)
    have tailSeparated : Separated (drop left 8) (drop right 8) := by
      intro off h
      simp only [drop_base, drop_len, same] at h ⊢
      have outside := separated (8 * n + off) (by omega)
      omega
    obtain ⟨updated, tailRun, tailBytes, tailFrame⟩ :=
      run_refines first permit (drop left 8) (drop right 8) tailSame
        (fun i => leftWords (n + i)) (fun i => rightWords (n + i))
        tailLeft tailRight tailWrite tailSeparated
    simp only [drop_base, drop_len] at tailBytes tailFrame
    refine ⟨updated, ?_, ?_, ?_⟩
    · have active : 0 < left.len.val ∧ 0 < right.len.val ∧
          0 < program.leftWidth ∧ 0 < program.rightWidth :=
        ⟨nonempty, by omega, by decide, by decide⟩
      rw [run]
      simp only [dite_eq_left active]
      change (runChunk permit (take left 8) (take right 8) program.ops [] heap).bind
        (run program permit (drop left 8) (drop right 8)) = _
      rw [firstRun, Option.bind_some]
      exact tailRun
    · intro i hi b
      by_cases firstChunk : i < n
      · rw [tailFrame _ (Or.inl (by have := b.isLt; omega))]
        exact firstBytes i firstChunk b
      · have offsetBound : i - n < left.len.val - 8 := by omega
        have offsetIndex : n + (i - n) = i := by omega
        have tailByte := tailBytes (i - n) offsetBound b
        change updated (left.base + 8 * n + 8 * (i - n) + b.val) = _ at tailByte
        rw [show left.base + 8 * n + 8 * (i - n) + b.val = left.base + 8 * i + b.val by omega] at tailByte
        simpa only [offsetIndex] using tailByte
    · intro address outside
      exact (tailFrame _ (by omega)).trans (firstFrame _ (by omega))
  · refine ⟨heap, ?_, ?_, fun _ _ => rfl⟩
    · rw [run]
      simp [nonempty]
    · intro i hi
      omega
termination_by left.len.val
decreasing_by
  simp only [drop_len]
  omega

/-- Exact byte representation of wordwise XOR on both admitted equal-length
views. All memory outside the destination, including the source, is framed. -/
def XorAssignContract : Prop :=
  ∀ (heap : Memory) (permit : Nat → Bool) (left right : Llbc.SliceView),
    right.len.val = left.len.val →
    ∀ (leftWords rightWords : Nat → BitVec 64),
      WordWindow heap left.base left.len.val leftWords →
      WordWindow heap right.base right.len.val rightWords →
      WritableWindow heap permit left.base left.len.val →
      Separated left right →
      ∃ updated : Memory,
        run program permit left right heap = some updated ∧
        WordWindow updated left.base left.len.val (fun index => leftWords index ^^^ rightWords index) ∧
        ∀ address, address < left.base ∨ left.base + 8 * left.len.val ≤ address →
          updated address = heap address

theorem xor_assign_refines : XorAssignContract := run_refines

end BulksketchBridge.AvxXorLlbc
