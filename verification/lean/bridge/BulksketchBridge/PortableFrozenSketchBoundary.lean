import BulksketchBridge.PortableSketchBoundary
import Arithmetic.RowLocalGenerated

namespace BulksketchBridge.PortableSketchBoundary

open Aeneas.Std Algebra.Gf64 Reconciliation
open bulksketch.sketch.shape (SketchShape)
open bulksketch.sketch.state (FrozenSketch)
open bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels (xor_assign)
open scoped symmDiff

abbrev NativeSketch := FrozenSketch bulksketch.field.Gf64
abbrev NativeShape := SketchShape bulksketch.field.Gf64

def capacities (shape : NativeShape) : List Nat :=
  shape.capacities.val.map UScalar.val

def rowStart (shape : NativeShape) (bucket : Nat) : Nat :=
  ((capacities shape).take bucket).sum

def rowWidth (shape : NativeShape) (bucket : Nat) : Nat :=
  (capacities shape)[bucket]!

/-- A borrowed row view of the original in-memory syndrome words. -/
def rowWords (sketch : NativeSketch) (bucket : Nat) : Slice U64 :=
  Slice.from (((sketch.state.words.val).drop (rowStart sketch.state.shape bucket)).take
    (rowWidth sketch.state.shape bucket)) (by
      rw [List.length_take, List.length_drop]
      exact (Nat.min_le_right ..).trans ((Nat.sub_le ..).trans (alloc.vec.Vec.property sketch.state.words)))

/-- The original in-memory zero flag is bit zero of the first zero word. -/
def zeroFlag (sketch : NativeSketch) : Bool :=
  (sketch.state.zero_words[0]! &&& 1#u64) != 0#u64

def rowZero (sketch : NativeSketch) (bucket : Nat) : Bool :=
  decide (bucket = 0) && zeroFlag sketch

/-- Validity for the original immutable in-memory state, using its exact
shape capacities, flattened syndrome words, and independent zero bit. -/
structure ValidFrozenSketch (ids : Finset U64) (sketch : NativeSketch) : Prop where
  bucketsPositive : 0 < sketch.state.shape.capacities.length
  capacitiesPositive : ∀ bucket < sketch.state.shape.capacities.length,
    0 < rowWidth sketch.state.shape bucket
  wordsSize : sketch.state.words.length = (capacities sketch.state.shape).sum
  zeroWordRoom : 0 < sketch.state.zero_words.length
  zero : zeroFlag sketch = true ↔ 0#u64 ∈ ids
  odd : ∀ bucket < sketch.state.shape.capacities.length,
    ∀ index < rowWidth sketch.state.shape bucket,
      toField (rowWords sketch bucket)[index]!.bv =
        oddSyndrome (nonzeroSupport (routedIds sketch.state.shape.capacities.length bucket ids)) index

private theorem row_range_admitted (shape : NativeShape) (bucket : Nat)
    (inside : bucket < shape.capacities.length) :
    rowStart shape bucket + rowWidth shape bucket ≤ (capacities shape).sum := by
  have available : bucket < (capacities shape).length := by
    simpa only [capacities, List.length_map, Slice.length] using inside
  have concat := List.take_succ_eq_append_getElem available
  have sums := congrArg List.sum concat
  rw [List.sum_append, List.sum_singleton] at sums
  have prefixBound : ((capacities shape).take (bucket + 1)).sum ≤ (capacities shape).sum := by
    rw [← List.sum_take_add_sum_drop (capacities shape) (bucket + 1)]
    exact Nat.le_add_right _ _
  rw [sums] at prefixBound
  unfold rowStart rowWidth
  rw [← List.Inhabited_getElem_eq_getElem! _ _ available]
  exact prefixBound

theorem rowWords_length (ids : Finset U64) (sketch : NativeSketch) (valid : ValidFrozenSketch ids sketch)
    (bucket : Nat) (inside : bucket < sketch.state.shape.capacities.length) :
    (rowWords sketch bucket).length = rowWidth sketch.state.shape bucket := by
  have room := row_range_admitted sketch.state.shape bucket inside
  rw [← valid.wordsSize] at room
  change rowStart sketch.state.shape bucket + rowWidth sketch.state.shape bucket ≤
    sketch.state.words.val.length at room
  unfold rowWords
  simp only [Slice.length, Slice.from_val, List.length_take, List.length_drop]
  exact Nat.min_eq_left (by omega)

theorem valid_frozen_row (ids : Finset U64) (sketch : NativeSketch)
    (valid : ValidFrozenSketch ids sketch) (bucket : Nat)
    (inside : bucket < sketch.state.shape.capacities.length) :
    ValidInMemoryRow (routedIds sketch.state.shape.capacities.length bucket ids)
      (rowWords sketch bucket) (rowZero sketch bucket) := by
  refine ⟨?_, ?_⟩
  · simp only [rowZero, Bool.and_eq_true, decide_eq_true_eq, valid.zero, routed_zero]
  · intro index indexBound
    rw [rowWords_length ids sketch valid bucket inside] at indexBound
    exact valid.odd bucket inside index indexBound

/-- The original Portable XOR kernel combines one admitted in-memory row of
two equal-shape immutable sketches and represents exactly that bucket's
symmetric difference, including its separate zero bit. -/
theorem portable_frozen_sketch_xor_at_bucket (leftIds rightIds : Finset U64)
    (left right : NativeSketch) (leftValid : ValidFrozenSketch leftIds left)
    (rightValid : ValidFrozenSketch rightIds right)
    (sameShape : left.state.shape = right.state.shape) (bucket : Nat)
    (inside : bucket < left.state.shape.capacities.length) :
    ∃ difference, xor_assign field (rowWords left bucket) (rowWords right bucket) = .ok difference ∧
      difference.length = rowWidth left.state.shape bucket ∧
      ValidInMemoryRow (routedIds left.state.shape.capacities.length bucket (leftIds ∆ rightIds))
        difference (Bool.xor (rowZero left bucket) (rowZero right bucket)) := by
  have rightInside : bucket < right.state.shape.capacities.length := by rw [← sameShape]; exact inside
  have leftRow := valid_frozen_row leftIds left leftValid bucket inside
  have rightRow := valid_frozen_row rightIds right rightValid bucket rightInside
  rw [← sameShape] at rightRow
  have sameWidth : (rowWords left bucket).length = (rowWords right bucket).length := by
    rw [rowWords_length leftIds left leftValid bucket inside,
      rowWords_length rightIds right rightValid bucket rightInside, sameShape]
  obtain ⟨difference, actual, width, valid⟩ :=
    portable_sketch_xor _ _ _ _ _ _ leftRow rightRow sameWidth
  rw [← routed_symmDiff] at valid
  exact ⟨difference, actual, width.trans (rowWords_length leftIds left leftValid bucket inside), valid⟩

#print axioms portable_frozen_sketch_xor_at_bucket

end BulksketchBridge.PortableSketchBoundary
