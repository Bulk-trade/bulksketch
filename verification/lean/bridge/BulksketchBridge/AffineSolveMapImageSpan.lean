import BulksketchBridge.AffineSolveMapPivotSpan
import BulksketchBridge.AffineSolveMapFiberAlgebra
import BulksketchBridge.AffineSolveMapTriangular
import BulksketchBridge.Algebra.Trace

namespace BulksketchBridge.AffineSolveMap

open Aeneas.Std Algebra.Gf64 FrobeniusTables AffineSubspaceAlgebra
open BulksketchProofs.Field.Period (xorPrefix xorPrefix_bits xorPrefix_complete)

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

noncomputable abbrev value (word : U64) : Field := toField word.bv

private theorem xor_value (x y : U64) : value (x ^^^ y) = value x + value y :=
  toField_xor _ _

private theorem value_injective : Function.Injective value := by
  intro left right same
  exact U64.bv_eq_imp_eq left right (toField_injective same)

theorem span_zero (basis : List Field) : 0 ∈ spanWords basis := by
  induction basis with
  | nil => exact rfl
  | cons direction earlier ih => exact Or.inl ih

theorem span_generator {basis : List Field} {point : Field} (member : point ∈ basis) :
    point ∈ spanWords basis := by
  induction basis with
  | nil => cases member
  | cons direction earlier ih =>
    rcases List.mem_cons.mp member with rfl | prior
    · exact Or.inr ⟨0, span_zero earlier, zero_add _⟩
    · exact Or.inl (ih prior)

theorem span_subset (source target : List Field)
    (contains : ∀ x ∈ source, x ∈ spanWords target) :
    spanWords source ⊆ spanWords target := by
  intro point member
  induction source generalizing point with
  | nil =>
    have zero : point = 0 := member
    rw [zero]
    exact span_zero target
  | cons direction earlier ih =>
    have old (x : Field) (inside : x ∈ earlier) : x ∈ spanWords target :=
      contains x (List.mem_cons_of_mem _ inside)
    rcases member with direct | ⟨prior, admitted, rfl⟩
    · exact ih old direct
    · exact span_add_closed target (ih old admitted) (contains direction (List.mem_cons_self ..))

def occupiedIndices (images : Columns) : List Nat :=
  (List.range 64).filter fun i => decide (entry images i ≠ 0#u64)

def occupiedRows (images : Columns) : List U64 :=
  (occupiedIndices images).map (entry images)

noncomputable def imageBasis (images : Columns) : List Field :=
  (occupiedRows images).map value

theorem mem_occupied {images : Columns} {row : U64} :
    row ∈ occupiedRows images ↔ ∃ i < 64, entry images i ≠ 0#u64 ∧ entry images i = row := by
  simp only [occupiedRows, occupiedIndices, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq]
  exact ⟨fun ⟨i, ⟨bound, live⟩, read⟩ => ⟨i, bound, live, read⟩,
    fun ⟨i, bound, live, read⟩ => ⟨i, ⟨bound, live⟩, read⟩⟩

theorem occupied_in_span (images : Columns) (i : Nat) (bound : i < 64)
    (live : entry images i ≠ 0#u64) : value (entry images i) ∈ spanWords (imageBasis images) := by
  apply span_generator
  exact List.mem_map_of_mem (f := value) (mem_occupied.mpr ⟨i, bound, live, rfl⟩)

private theorem ordered_occupied (images : Columns) (valid : Pivots images) :
    (occupiedRows images).Pairwise fun left right => pivot left < pivot right := by
  unfold occupiedRows
  rw [List.pairwise_map]
  have ordered : (occupiedIndices images).Pairwise (· < ·) := List.pairwise_lt_range.filter _
  apply ordered.imp_of_mem
  intro i j hi hj less
  have info (i : Nat) (member : i ∈ occupiedIndices images) : i < 64 ∧ entry images i ≠ 0#u64 := by
    simpa only [occupiedIndices, List.mem_filter, List.mem_range, decide_eq_true_eq] using member
  obtain ⟨iBound, iLive⟩ := info i hi
  obtain ⟨jBound, jLive⟩ := info j hj
  rw [valid i iBound iLive, valid j jBound jLive]
  exact less

private theorem span_is_sublist_xor (rows : List U64) (point : Field)
    (member : point ∈ spanWords (rows.map value)) :
    ∃ selected : List U64, selected.Sublist rows ∧ value (xorRowSum selected) = point := by
  induction rows generalizing point with
  | nil =>
    have zero : point = 0 := member
    refine ⟨[], List.Sublist.refl _, ?_⟩
    rw [zero]
    exact toField_zero
  | cons row rows ih =>
    change point ∈ spanWords (value row :: rows.map value) at member
    rcases member with direct | ⟨prior, direct, rfl⟩
    · obtain ⟨selected, sublist, sum⟩ := ih point direct
      exact ⟨selected, sublist.cons _, sum⟩
    · obtain ⟨selected, sublist, sum⟩ := ih prior direct
      refine ⟨row :: selected, sublist.cons_cons _, ?_⟩
      change value (row ^^^ xorRowSum selected) = _
      rw [xor_value, sum, add_comm]

theorem vacant_not_in_span (images : Columns) (valid : Pivots images) (final : U64)
    (live : final ≠ 0#u64) (vacant : entry images (pivot final) = 0#u64) :
    value final ∉ spanWords (imageBasis images) := by
  intro member
  obtain ⟨selected, sublist, sum⟩ := span_is_sublist_xor (occupiedRows images) (value final) member
  have found (row : U64) (contains : row ∈ selected) :
      entry images (pivot row) = row ∧ row ≠ 0#u64 := by
    obtain ⟨i, fits, present, read⟩ := mem_occupied.mp (sublist.subset contains)
    subst row
    rw [valid i fits present]
    exact ⟨rfl, present⟩
  exact vacant_residue_excludes images final live vacant selected found
    ((ordered_occupied images valid).sublist sublist) (value_injective sum)

theorem reduction_image_difference {images preimages : Columns} {original image reduced final : U64}
    (path : Reduced images preimages original image reduced final) :
    value image + value final ∈ spanWords (imageBasis images) := by
  induction path with
  | zero =>
    change (0 : Field) + 0 ∈ _
    rw [add_zero]
    exact span_zero _
  | vacant =>
    rw [CharTwo.add_self_eq_zero]
    exact span_zero _
  | cancel _ image _ final live occupied _ ih =>
    rw [xor_value] at ih
    have fromPivot := occupied_in_span images (pivot image) (pivot_lt_width image live) occupied
    have combined := span_add_closed (imageBasis images) ih fromPivot
    have cancel : (value image + value (entry images (pivot image)) + value final) +
        value (entry images (pivot image)) = value image + value final := by
      calc
        _ = (value image + value final) +
          (value (entry images (pivot image)) + value (entry images (pivot image))) := by ac_rfl
        _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]
    rwa [cancel] at combined

theorem inserted_pivots (images : Columns) (valid : Pivots images) (final : U64) :
    Pivots (inserted images final final) := by
  by_cases zero : final = 0#u64
  · simpa only [inserted, zero, ite_true] using valid
  · simp only [inserted, zero, ite_false]
    intro i bound live
    by_cases written : i = (pivotWord final).val
    · subst i
      rw [entry_set_same _ _ _ bound, pivot_word_val]
    · rw [entry_set_other _ _ _ _ (Ne.symm written)] at live ⊢
      exact valid i bound live

private theorem insert_read_same (images : Columns) (final : U64) (live : final ≠ 0#u64) :
    entry (inserted images final final) (pivotWord final).val = final := by
  have bound : (pivotWord final).val < (64#usize).val := by
    rw [pivot_word_val]
    exact pivot_lt_width final live
  rw [inserted, ite_eq_right live]
  exact entry_set_same images (pivotWord final) final bound

private theorem insert_read_other (images : Columns) (final : U64) (live : final ≠ 0#u64)
    (i : Nat) (different : (pivotWord final).val ≠ i) :
    entry (inserted images final final) i = entry images i := by
  rw [inserted, ite_eq_right live]
  exact entry_set_other images (pivotWord final) i final different

theorem insert_span (images : Columns) (final : U64) (live : final ≠ 0#u64)
    (vacant : entry images (pivot final) = 0#u64) :
    spanWords (imageBasis (inserted images final final)) =
      spanWords (value final :: imageBasis images) := by
  apply Set.Subset.antisymm
  · apply span_subset
    intro point generator
    obtain ⟨row, inRows, rfl⟩ := List.mem_map.mp generator
    obtain ⟨i, bound, present, read⟩ := mem_occupied.mp inRows
    by_cases written : i = (pivotWord final).val
    · subst i
      rw [insert_read_same images final live] at read
      rw [← read]
      exact span_generator (List.mem_cons_self ..)
    · rw [insert_read_other images final live i (Ne.symm written)] at present read
      rw [← read]
      exact Or.inl (occupied_in_span images i bound present)
  · apply span_subset
    intro point generator
    rcases List.mem_cons.mp generator with rfl | earlier
    · have bound : (pivotWord final).val < 64 := by
        rw [pivot_word_val]
        exact pivot_lt_width final live
      have installed := insert_read_same images final live
      have present : entry (inserted images final final) (pivotWord final).val ≠ 0#u64 := by
        rwa [installed]
      have found := occupied_in_span (inserted images final final) (pivotWord final).val bound present
      rwa [installed] at found
    · obtain ⟨row, inRows, rfl⟩ := List.mem_map.mp earlier
      obtain ⟨i, bound, present, read⟩ := mem_occupied.mp inRows
      have old : (pivotWord final).val ≠ i := by
        intro written
        rw [pivot_word_val] at written
        apply present
        rw [← written]
        exact vacant
      have unchanged := insert_read_other images final live i old
      have still : entry (inserted images final final) i ≠ 0#u64 := by rwa [unchanged]
      have found := occupied_in_span (inserted images final final) i bound still
      rwa [unchanged, read] at found

noncomputable def inputBasis : Nat → List Field
  | 0 => []
  | n + 1 => value (basisBit n) :: inputBasis n

private theorem prefix_in_input_span (word : BitVec 64) (width : Nat) :
    toField (xorPrefix word width) ∈ spanWords (inputBasis width) := by
  induction width with
  | zero => exact toField_zero
  | succ width ih =>
    unfold inputBasis
    rw [xorPrefix, toField_xor]
    by_cases set : word.getLsbD width
    · rw [ite_eq_left set]
      exact Or.inr ⟨_, ih, rfl⟩
    · rw [ite_eq_right set, toField_zero, add_zero]
      exact Or.inl ih

theorem low_in_input_span (word : U64) (width : Nat) (low : word.val < 2 ^ width) :
    value word ∈ spanWords (inputBasis width) := by
  have complete : xorPrefix word.bv width = word.bv := by
    apply BitVec.eq_of_getLsbD_eq
    intro i bound
    rw [xorPrefix_bits word.bv width i bound]
    by_cases below : i < width
    · rw [ite_eq_left below]
    · rw [ite_eq_right below]
      have iFits : word.val < 2 ^ i :=
        low.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt below))
      exact (Nat.testBit_lt_two_pow iFits).symm
  simpa only [complete] using prefix_in_input_span word.bv width

theorem input_basis_spans (point : Field) : point ∈ spanWords (inputBasis 64) := by
  let word := wordFieldEquiv.symm point
  have all := prefix_in_input_span word 64
  rw [xorPrefix_complete, show toField word = point from wordFieldEquiv.apply_symm_apply _] at all
  exact all

#print axioms vacant_not_in_span
#print axioms reduction_image_difference
#print axioms insert_span
#print axioms input_basis_spans

end BulksketchBridge.AffineSolveMap
