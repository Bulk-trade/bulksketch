import BulksketchBridge.AffineSolveMapImageSpan

namespace BulksketchBridge.AffineSolveMap

open Aeneas Aeneas.Std Algebra.Gf64 FrobeniusTables AffineSubspaceAlgebra
open bulksketch.backend.contract bulksketch.decode.affine

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

noncomputable def fieldLift (map : U64 → U64) (point : Field) : Field :=
  value (map ⟨wordFieldEquiv.symm point⟩)

theorem field_lift_word (map : U64 → U64) (word : U64) :
    fieldLift map (value word) = value (map word) := by
  unfold fieldLift
  change value (map ⟨wordFieldEquiv.symm (wordFieldEquiv word.bv)⟩) = _
  rw [wordFieldEquiv.symm_apply_apply]

theorem field_lift_zero (map : U64 → U64) (linear : XorLinear map) :
    fieldLift map 0 = 0 := by
  rw [← show value 0#u64 = 0 from toField_zero, field_lift_word, linear.1]

theorem field_lift_add (map : U64 → U64) (linear : XorLinear map) (x y : Field) :
    fieldLift map (x + y) = fieldLift map x + fieldLift map y := by
  let a : U64 := ⟨wordFieldEquiv.symm x⟩
  let b : U64 := ⟨wordFieldEquiv.symm y⟩
  have left : value a = x := wordFieldEquiv.apply_symm_apply _
  have right : value b = y := wordFieldEquiv.apply_symm_apply _
  have xor : value (a ^^^ b) = value a + value b := toField_xor _ _
  rw [← left, ← right, ← xor, field_lift_word, linear.2, field_lift_word, field_lift_word]
  exact toField_xor _ _

noncomputable def ImageThrough (map : U64 → U64) (images : Columns) (width : Nat) : Prop :=
  fieldLift map '' spanWords (inputBasis width) = spanWords (imageBasis images)

private theorem map_span_push (map : Field → Field) (additive : ∀ x y, map (x + y) = map x + map y)
    (direction : Field) (inputs rows : List Field)
    (prior : map '' spanWords inputs = spanWords rows) :
    map '' spanWords (direction :: inputs) = spanWords (map direction :: rows) := by
  ext point
  constructor
  · rintro ⟨source, choice, rfl⟩
    rcases choice with old | ⟨before, old, rfl⟩
    · exact Or.inl (prior ▸ (show map source ∈ map '' spanWords inputs from ⟨source, old, rfl⟩))
    · have image : map before ∈ spanWords rows :=
        prior ▸ (show map before ∈ map '' spanWords inputs from ⟨before, old, rfl⟩)
      exact Or.inr ⟨map before, image, (additive ..).symm⟩
  · intro member
    rcases member with old | ⟨before, old, rfl⟩
    · obtain ⟨source, sourceIn, exactPoint⟩ := (prior.symm ▸ old : point ∈ map '' spanWords inputs)
      exact ⟨source, Or.inl sourceIn, exactPoint⟩
    · obtain ⟨source, sourceIn, exactPoint⟩ := (prior.symm ▸ old : before ∈ map '' spanWords inputs)
      exact ⟨source + direction, Or.inr ⟨source, sourceIn, rfl⟩, by rw [additive, exactPoint]⟩

private theorem span_absorb (rows : List Field) (point : Field)
    (already : point ∈ spanWords rows) :
    spanWords (point :: rows) = spanWords rows := by
  apply Set.Subset.antisymm
  · apply span_subset
    intro value member
    rcases List.mem_cons.mp member with rfl | inRows
    · exact already
    · exact span_generator inRows
  · exact fun _ member => Or.inl member

private theorem span_rebase (rows : List Field) (first second : Field)
    (difference : first + second ∈ spanWords rows) :
    spanWords (first :: rows) = spanWords (second :: rows) := by
  have remove (a b : Field) : a + b + b = a := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  apply Set.Subset.antisymm
  · apply span_subset
    intro point member
    rcases List.mem_cons.mp member with equal | inRows
    · rw [equal]
      exact Or.inr ⟨first + second, difference, remove ..⟩
    · exact Or.inl (span_generator inRows)
  · apply span_subset
    intro point member
    rcases List.mem_cons.mp member with equal | inRows
    · rw [equal]
      exact Or.inr ⟨first + second, difference,
        (congrArg (fun x : Field => x + first) (add_comm first second)).trans (remove second first)⟩
    · exact Or.inl (span_generator inRows)

theorem image_through_empty (map : U64 → U64) (linear : XorLinear map) :
    ImageThrough map (Array.repeat 64#usize 0#u64) 0 := by
  let images : Columns := Array.repeat 64#usize 0#u64
  have empty : occupiedRows images = [] := by
    cases actual : occupiedRows images with
    | nil => rfl
    | cons row rest =>
      have inside : row ∈ occupiedRows images := by rw [actual]; exact List.mem_cons_self ..
      obtain ⟨i, bound, live, _⟩ := mem_occupied.mp inside
      exact (live (entry_repeat _ _ _ bound)).elim
  change fieldLift map '' spanWords (inputBasis 0) = spanWords (imageBasis images)
  rw [imageBasis, empty]
  simp only [inputBasis, List.map_nil, spanWords, Set.image_singleton, field_lift_zero map linear]

private theorem image_push_dependent {images preimages : Columns} {column reduced : U64}
    (map : U64 → U64) (linear : XorLinear map) (index : Nat)
    (prior : ImageThrough map images index) (meaning : map (basisBit index) = column)
    (path : Reduced images preimages (basisBit index) column reduced 0#u64) :
    ImageThrough map images (index + 1) := by
  have difference := reduction_image_difference path
  rw [show value 0#u64 = 0 from toField_zero, add_zero] at difference
  change fieldLift map '' spanWords (value (basisBit index) :: inputBasis index) = _
  rw [map_span_push _ (field_lift_add map linear) _ _ _ prior, field_lift_word, meaning]
  exact span_absorb _ _ difference

private theorem image_push_independent {images preimages : Columns} {column reduced final : U64}
    (map : U64 → U64) (linear : XorLinear map) (index : Nat)
    (prior : ImageThrough map images index) (meaning : map (basisBit index) = column)
    (path : Reduced images preimages (basisBit index) column reduced final) (live : final ≠ 0#u64) :
    ImageThrough map (inserted images final final) (index + 1) := by
  have vacant := (reduced_terminal path).resolve_left live
  have difference := reduction_image_difference path
  change fieldLift map '' spanWords (value (basisBit index) :: inputBasis index) = _
  rw [map_span_push _ (field_lift_add map linear) _ _ _ prior, field_lift_word, meaning,
    insert_span _ _ live vacant]
  exact span_rebase _ _ _ difference

theorem column_trace_order {columns : Slice U64} {start stop : Nat} {before after : EliminationState}
    (trace : ColumnTrace columns start before stop after) : start ≤ stop := by
  induction trace <;> omega

/-- The occupied image slots span exactly the images of all processed native
basis columns, with no added or lost directions. -/
theorem elimination_image_span {columns : Slice U64} {start stop : Nat} {before after : EliminationState}
    (trace : ColumnTrace columns start before stop after)
    (map : U64 → U64) (linear : XorLinear map)
    (values : ∀ i < 64, map (basisBit i) = columns[i]!)
    (stopBound : stop ≤ 64) (beforeSpan : ImageThrough map before.images start) :
    ImageThrough map after.images stop := by
  induction trace with
  | finished => exact beforeSpan
  | dependent index state reduced rank path increment stop output rest ih =>
    have indexBound : index < 64 := (column_trace_order rest).trans stopBound
    exact ih stopBound (image_push_dependent map linear index beforeSpan (values index indexBound) path)
  | independent index state reduced final path live stop output rest ih =>
    have indexBound : index < 64 := (column_trace_order rest).trans stopBound
    exact ih stopBound (image_push_independent map linear index beforeSpan (values index indexBound) path live)

theorem failed_target_excludes {images preimages : Columns} {target reduced final : U64}
    (map : U64 → U64) (valid : Pivots images)
    (through : ImageThrough map images 64)
    (reduction : Reduced images preimages 0#u64 target reduced final) (live : final ≠ 0#u64) :
    ¬ ∃ x : Field, fieldLift map x = value target := by
  rintro ⟨x, mapped⟩
  have targetSpan : value target ∈ spanWords (imageBasis images) :=
    through ▸ (show value target ∈ fieldLift map '' spanWords (inputBasis 64) from
      ⟨x, input_basis_spans x, mapped⟩)
  have difference := reduction_image_difference reduction
  have combined := span_add_closed _ targetSpan difference
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add] at combined
  exact vacant_not_in_span images valid final live ((reduced_terminal reduction).resolve_left live) combined

#print axioms elimination_image_span
#print axioms failed_target_excludes

end BulksketchBridge.AffineSolveMap
