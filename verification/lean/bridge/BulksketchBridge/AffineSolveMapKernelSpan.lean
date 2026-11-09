import BulksketchBridge.AffineSolveMapImageThrough

namespace BulksketchBridge.AffineSolveMap

open Aeneas.Std Algebra.Gf64 FrobeniusTables AffineSubspaceAlgebra
open AffineSubspaces (prefixDirections)

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

noncomputable def kernelBasis (state : EliminationState) : List Field :=
  prefixDirections state.kernel.to_slice state.rank.val

noncomputable def KernelThrough (map : U64 → U64) (state : EliminationState) (width : Nat) : Prop :=
  KernelBasis (fieldLift map) (inputBasis width) (kernelBasis state)

private theorem array_slice_read (array : Columns) (i : Nat) : array.to_slice[i]! = entry array i := by
  simp only [Slice.getElem!_Nat_eq, Array.to_slice, Slice.from_val, entry]

theorem prefix_directions_congr (left right : Slice U64) (width : Nat)
    (words : ∀ i < width, left[i]! = right[i]!) :
    prefixDirections left width = prefixDirections right width := by
  induction width with
  | zero => rfl
  | succ n ih =>
    simp only [prefixDirections]
    rw [words n (Nat.lt_succ_self n), ih (fun i hi => words i (hi.trans (Nat.lt_succ_self n)))]

private theorem kernel_push (state : EliminationState) (rank : Usize) (word : U64)
    (increment : rank.val = state.rank.val + 1) (room : state.rank.val < 64) :
    kernelBasis { state with kernel := state.kernel.set state.rank word, rank := rank } =
      value word :: kernelBasis state := by
  change prefixDirections (state.kernel.set state.rank word).to_slice rank.val = _
  rw [increment, prefixDirections]
  have head : (state.kernel.set state.rank word).to_slice[state.rank.val]! = word := by
    rw [array_slice_read]
    exact entry_set_same state.kernel state.rank word (by exact room)
  rw [head]
  have tail : prefixDirections (state.kernel.set state.rank word).to_slice state.rank.val =
      prefixDirections state.kernel.to_slice state.rank.val := by
    apply prefix_directions_congr
    intro i older
    rw [array_slice_read, array_slice_read]
    exact entry_set_other state.kernel state.rank i word (by omega)
  rw [tail]
  rfl

theorem kernel_through_empty (map : U64 → U64) (linear : XorLinear map) (scratch : Columns) :
    KernelThrough map (initialElimination scratch) 0 := by
  intro point
  change point = 0 ↔ point = 0 ∧ fieldLift map point = 0
  constructor
  · intro zero
    exact ⟨zero, by rw [zero]; exact field_lift_zero map linear⟩
  · exact And.left

private theorem sum_zero_equal {x y : Field} (zero : x + y = 0) : x = y := by
  calc
    x = (x + y) + y := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = y := by rw [zero, zero_add]

private theorem dependent_correction {state : EliminationState} {column reduced : U64}
    (map : U64 → U64) (linear : XorLinear map) (index : Nat)
    (graph : Graph map state.images state.preimages) (preimages : PreimagesBelow state index)
    (meaning : map (basisBit index) = column)
    (path : Reduced state.images state.preimages (basisBit index) column reduced 0#u64) :
    ∃ prior : Field, prior ∈ spanWords (inputBasis index) ∧
      value reduced = value (basisBit index) + prior ∧
      fieldLift map (value (basisBit index)) = fieldLift map prior := by
  obtain ⟨low, fits, correction⟩ := reduced_witness_below path index preimages
  have valueCorrection : value reduced = value (basisBit index) + value low := by
    rw [correction]
    exact toField_xor _ _
  refine ⟨value low, low_in_input_span low index fits, valueCorrection, ?_⟩
  apply sum_zero_equal
  rw [← field_lift_add map linear, ← valueCorrection, field_lift_word, reduce_graph map linear graph path meaning]
  exact toField_zero

private theorem independent_image {state : EliminationState} {column reduced final : U64}
    (map : U64 → U64) (index : Nat) (images : ImageThrough map state.images index)
    (pivots : Pivots state.images) (meaning : map (basisBit index) = column)
    (path : Reduced state.images state.preimages (basisBit index) column reduced final) (live : final ≠ 0#u64) :
    fieldLift map (value (basisBit index)) ∉ fieldLift map '' spanWords (inputBasis index) := by
  unfold ImageThrough at images
  rw [field_lift_word, meaning, images]
  intro old
  have difference := reduction_image_difference path
  have combined := span_add_closed _ old difference
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add] at combined
  exact vacant_not_in_span state.images pivots final live ((reduced_terminal path).resolve_left live) combined

structure SweepSpans (map : U64 → U64) (state : EliminationState) (width : Nat) : Prop where
  graph : Graph map state.images state.preimages
  preimages : PreimagesBelow state width
  triangular : KernelTriangular state width
  pivots : Pivots state.images
  image : ImageThrough map state.images width
  kernel : KernelThrough map state width

theorem sweep_spans_empty (map : U64 → U64) (linear : XorLinear map) (scratch : Columns) :
    SweepSpans map (initialElimination scratch) 0 := by
  refine ⟨?_, ?_, ?_, empty_pivots, image_through_empty map linear, kernel_through_empty map linear scratch⟩
  · intro i fits present
    change entry (Array.repeat 64#usize 0#u64) i ≠ 0#u64 at present
    exact (present (entry_repeat _ _ _ fits)).elim
  · intro i fits present
    change entry (Array.repeat 64#usize 0#u64) i ≠ 0#u64 at present
    exact (present (entry_repeat _ _ _ fits)).elim
  · intro i written
    change i < 0 at written
    omega

/-- The exact source sweep spans the whole restricted kernel. A dependent
column contributes its new basis bit plus a preimage from earlier bits. -/
theorem elimination_kernel_span {columns : Slice U64} {start stop : Nat} {before after : EliminationState}
    (trace : ColumnTrace columns start before stop after)
    (map : U64 → U64) (linear : XorLinear map)
    (values : ∀ i < 64, map (basisBit i) = columns[i]!)
    (stopBound : stop ≤ 64) (rankBound : before.rank.val ≤ start)
    (prior : SweepSpans map before start) :
    SweepSpans map after stop := by
  induction trace with
  | finished => exact prior
  | dependent index state reduced rank path increment stop output rest ih =>
    have indexBound : index < 64 := (column_trace_order rest).trans stopBound
    let updated : EliminationState := { state with kernel := state.kernel.set state.rank reduced, rank := rank }
    have single : ColumnTrace columns index state (index + 1) updated :=
      .dependent index state reduced rank path increment (index + 1) updated (.finished _ _)
    have width : index + 1 ≤ 64 := indexBound
    have rankNext : updated.rank.val ≤ index + 1 := by change rank.val ≤ index + 1; omega
    obtain ⟨preimages, triangular⟩ := elimination_triangular single width rankBound prior.preimages prior.triangular
    have image := elimination_image_span single map linear values width prior.image
    obtain ⟨old, oldIn, correction, same⟩ :=
      dependent_correction map linear index prior.graph prior.preimages (values index indexBound) path
    have kernel : KernelThrough map updated (index + 1) := by
      unfold KernelThrough
      rw [inputBasis, kernel_push state rank reduced increment (by omega), correction]
      exact extend_dependent_image _ (field_lift_add map linear) _ _ _ _ prior.kernel oldIn same
    exact ih stopBound rankNext ⟨prior.graph, preimages, triangular, prior.pivots, image, kernel⟩
  | independent index state reduced final path live stop output rest ih =>
    have indexBound : index < 64 := (column_trace_order rest).trans stopBound
    let updated : EliminationState := { state with
      images := inserted state.images final final
      preimages := inserted state.preimages final reduced }
    have single : ColumnTrace columns index state (index + 1) updated :=
      .independent index state reduced final path live (index + 1) updated (.finished _ _)
    have width : index + 1 ≤ 64 := indexBound
    have rankNext : updated.rank.val ≤ index + 1 := by change state.rank.val ≤ index + 1; omega
    obtain ⟨preimages, triangular⟩ := elimination_triangular single width rankBound prior.preimages prior.triangular
    have image := elimination_image_span single map linear values width prior.image
    have mapped := reduce_graph map linear prior.graph path (values index indexBound)
    have graph : Graph map updated.images updated.preimages := insert_graph map prior.graph mapped
    have pivots : Pivots updated.images := inserted_pivots _ prior.pivots final
    have outside := independent_image map index prior.image prior.pivots (values index indexBound) path live
    have kernel : KernelThrough map updated (index + 1) :=
      extend_independent_image _ (field_lift_add map linear) _ _ _ prior.kernel outside
    exact ih stopBound rankNext ⟨graph, preimages, triangular, pivots, image, kernel⟩

theorem complete_kernel {map : U64 → U64} {state : EliminationState}
    (basis : KernelThrough map state 64) (point : Field) :
    fieldLift map point = 0 ↔ point ∈ spanWords (kernelBasis state) := by
  rw [basis point]
  exact ⟨fun zero => ⟨input_basis_spans point, zero⟩, And.right⟩

#print axioms elimination_kernel_span
#print axioms complete_kernel

end BulksketchBridge.AffineSolveMap
