import BulksketchBridge.PortableXor
import BulksketchBridge.SyndromeUniqueness
import BulksketchBridge.RebuiltLocatorPolynomial
import Arithmetic.CompletedResultGenerated
import BulksketchBridge.CandidateBucket

namespace BulksketchBridge.PortableSketchBoundary

open Aeneas.Std Algebra.Gf64 Reconciliation RebuiltLfsr
open bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels (xor_assign)
open bulksketch.decode.row (RowResult RowBudget)
open scoped symmDiff

abbrev field := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField

noncomputable def wordEmbedding : U64 ↪ Field :=
  ⟨fun word => toField word.bv,
    fun a b equal => U64.bv_eq_imp_eq a b (toField_injective equal)⟩

/-- The original row algebra keeps the zero bit separate from its odd words. -/
noncomputable def nonzeroSupport (ids : Finset U64) : Finset Field :=
  (ids.erase 0#u64).map wordEmbedding

structure ValidInMemoryRow (ids : Finset U64) (words : Slice U64) (hasZero : Bool) : Prop where
  zero : hasZero = true ↔ 0#u64 ∈ ids
  odd : ∀ index < words.length, toField words[index]!.bv = oddSyndrome (nonzeroSupport ids) index

theorem nonzeroSupport_no_zero (ids : Finset U64) : (0 : Field) ∉ nonzeroSupport ids := by
  intro member
  obtain ⟨word, inside, equal⟩ := Finset.mem_map.mp member
  have zero : word = 0#u64 := wordEmbedding.injective (equal.trans toField_zero.symm)
  exact (Finset.mem_erase.mp inside).1 zero

theorem nonzeroSupport_card (ids : Finset U64) :
    (nonzeroSupport ids).card = (ids.erase 0#u64).card :=
  Finset.card_map _

theorem nonzeroSupport_symmDiff (left right : Finset U64) :
    nonzeroSupport (left ∆ right) = nonzeroSupport left ∆ nonzeroSupport right := by
  classical
  have erase : (left ∆ right).erase 0#u64 = left.erase 0#u64 ∆ right.erase 0#u64 := by
    ext word
    simp only [Finset.mem_erase, Finset.mem_symmDiff]
    by_cases nonzero : word = 0#u64 <;> simp [nonzero]
  unfold nonzeroSupport
  rw [erase]
  simp only [Finset.symmDiff_def, Finset.map_union, Finset.map_sdiff]

theorem zero_flag_symmDiff (left right : Finset U64) (leftZero rightZero : Bool)
    (leftHasZero : leftZero = true ↔ 0#u64 ∈ left)
    (rightHasZero : rightZero = true ↔ 0#u64 ∈ right) :
    Bool.xor leftZero rightZero = true ↔ 0#u64 ∈ left ∆ right := by
  rw [Finset.mem_symmDiff, ← leftHasZero, ← rightHasZero]
  cases leftZero <;> cases rightZero <;> decide

/-- The existing checked original Portable in-memory XOR kernel combines
the two rows' algebraic words. The separate zero bit follows the original
membership XOR rule. -/
theorem portable_sketch_xor (left right : Finset U64) (leftWords rightWords : Slice U64)
    (leftZero rightZero : Bool) (leftValid : ValidInMemoryRow left leftWords leftZero)
    (rightValid : ValidInMemoryRow right rightWords rightZero)
    (sameWidth : leftWords.length = rightWords.length) :
    ∃ difference, xor_assign field leftWords rightWords = .ok difference ∧
      difference.length = leftWords.length ∧
      ValidInMemoryRow (left ∆ right) difference (Bool.xor leftZero rightZero) := by
  obtain ⟨difference, actual, width, words⟩ :=
    (PortableXor.xor_assign_refines _ field leftWords rightWords).1 sameWidth
  refine ⟨difference, actual, width, zero_flag_symmDiff left right leftZero rightZero leftValid.zero rightValid.zero, ?_⟩
  intro i inside
  have leftBound : i < leftWords.length := by rwa [← width]
  have rightBound : i < rightWords.length := by rwa [← sameWidth]
  rw [words i leftBound]
  change toField (leftWords[i]!.bv ^^^ rightWords[i]!.bv) = _
  rw [toField_xor, leftValid.odd i leftBound, rightValid.odd i rightBound,
    nonzeroSupport_symmDiff]
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  classical
  simp only [oddSyndrome, powerSum_symmDiff]

private theorem support_list_map (roots : Slice U64) :
    roots.val.toFinset.map wordEmbedding = rootSupport roots := by
  classical
  apply Finset.ext
  intro point
  simp only [rootSupport, Finset.mem_map, List.mem_toFinset, List.mem_map]
  rfl

theorem recovered_nonzero_ids (ids : Finset U64) (roots : Slice U64)
    (exact : rootSupport roots = nonzeroSupport ids) :
    roots.val.toFinset = ids.erase 0#u64 := by
  apply Finset.map_injective wordEmbedding
  rw [support_list_map, exact]
  rfl

/-- The list denoted by the original row result and its independently tracked
zero difference bit. The original publication convention prepends zero to
a decoded row and supplies no IDs for Equal. -/
def decodedIds (zeroDiff : Bool) (result : RowResult) : Option (List U64) :=
  match result with
  | .Equal => some []
  | .Decoded roots => some (if zeroDiff then 0#u64 :: roots.val else roots.val)
  | .Failed _ => none

theorem decoded_ids_exact (ids : Finset U64) (roots : Slice U64) (zeroDiff : Bool)
    (zero : zeroDiff = true ↔ 0#u64 ∈ ids)
    (support : rootSupport roots = nonzeroSupport ids) (distinct : roots.val.Nodup) :
    let result := if (nonzeroSupport ids).card = 0 ∧ zeroDiff = false then RowResult.Equal else RowResult.Decoded roots
    ∃ output, decodedIds zeroDiff result = some output ∧ output.Nodup ∧ output.toFinset = ids := by
  have members := recovered_nonzero_ids ids roots support
  have rootsNonzero : 0#u64 ∉ roots.val := by
    intro present
    have present' := List.mem_toFinset.mpr present
    rw [members] at present'
    exact Finset.notMem_erase _ _ present'
  dsimp only
  cases zeroValue : zeroDiff
  · have absent : 0#u64 ∉ ids := by
      intro present
      have impossible := zero.mpr present
      simp [zeroValue] at impossible
    have full : roots.val.toFinset = ids := members.trans (Finset.erase_eq_of_notMem absent)
    by_cases empty : (nonzeroSupport ids).card = 0
    · have noIds : ids = ∅ := by
        apply Finset.card_eq_zero.mp
        rw [nonzeroSupport_card, Finset.erase_eq_of_notMem absent] at empty
        exact empty
      exact ⟨[], by simp [empty, decodedIds], List.nodup_nil, by simp [noIds]⟩
    · exact ⟨roots.val, by simp [empty, decodedIds], distinct, full⟩
  · have present : 0#u64 ∈ ids := zero.mp zeroValue
    refine ⟨0#u64 :: roots.val, by simp [decodedIds],
      List.nodup_cons.mpr ⟨rootsNonzero, distinct⟩, ?_⟩
    rw [List.toFinset_cons, members, Finset.insert_erase present]

def zeroCost (zero : Bool) : Nat := if zero then 1 else 0

theorem support_card_add_zeroCost (ids : Finset U64) (zero : Bool)
    (membership : zero = true ↔ 0#u64 ∈ ids) :
    (nonzeroSupport ids).card + zeroCost zero = ids.card := by
  rw [nonzeroSupport_card]
  cases zero
  · have absent : 0#u64 ∉ ids := by
      intro present
      exact Bool.noConfusion (membership.mpr present)
    simp [zeroCost, Finset.erase_eq_of_notMem absent]
  · exact Finset.card_erase_add_one (membership.mp rfl)

theorem row_budget_total_eq_nonzero (budget : RowBudget) (zero : Bool)
    (reserved : budget.total.val = budget.nonzero.val + zeroCost zero) :
    budget.total = budget.nonzero ↔ zero = false := by
  cases zero
  · simp only [zeroCost, Bool.false_eq_true, ite_false, Nat.add_zero] at reserved
    exact ⟨fun _ => rfl, fun _ => UScalar.eq_of_val_eq reserved⟩
  · constructor
    · intro same
      rw [same] at reserved
      simp [zeroCost] at reserved
    · intro impossible
      cases impossible

theorem decoded_ids_exact_at_budget (ids : Finset U64) (roots : Slice U64)
    (zero : Bool) (budget : RowBudget)
    (membership : zero = true ↔ 0#u64 ∈ ids)
    (reserved : budget.total.val = budget.nonzero.val + zeroCost zero)
    (support : rootSupport roots = nonzeroSupport ids) (distinct : roots.val.Nodup) :
    let result := if (nonzeroSupport ids).card = 0 ∧ budget.total = budget.nonzero
      then RowResult.Equal else RowResult.Decoded roots
    ∃ output, decodedIds zero result = some output ∧ output.Nodup ∧ output.toFinset = ids := by
  simpa only [row_budget_total_eq_nonzero budget zero reserved] using
    decoded_ids_exact ids roots zero membership support distinct

/-- A budget-bounded row with no changed syndrome words and no changed
zero bit is the empty difference. This is the original Equal shortcut. -/
theorem equal_words_and_flag_iff_empty (ids : Finset U64) (words : Slice U64) (zero : Bool)
    (valid : ValidInMemoryRow ids words zero)
    (bounded : (nonzeroSupport ids).card ≤ words.length) :
    (zero = false ∧ ∀ i < words.length, words[i]! = 0#u64) ↔ ids = ∅ := by
  classical
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  constructor
  · intro ⟨noZeroDiff, zeroWords⟩
    have absent : 0#u64 ∉ ids := by
      intro present
      have hasZero := valid.zero.mpr present
      rw [noZeroDiff] at hasZero
      cases hasZero
    have emptySupport : nonzeroSupport ids = ∅ := by
      apply eq_of_oddSyndromes_eq words.length _ _ bounded (by simp)
        (nonzeroSupport_no_zero ids) (by simp)
      intro i inside
      rw [← valid.odd i inside, zeroWords i inside]
      simp only [oddSyndrome, powerSum, Finset.sum_empty]
      exact toField_zero
    apply Finset.card_eq_zero.mp
    rw [← Finset.erase_eq_of_notMem absent, ← nonzeroSupport_card, emptySupport]
    rfl
  · rintro rfl
    have noZeroDiff : zero = false := by
      cases value : zero
      · rfl
      · have impossible := valid.zero.mp value
        simp at impossible
    refine ⟨noZeroDiff, ?_⟩
    intro i inside
    apply wordEmbedding.injective
    change toField words[i]!.bv = toField (0#u64).bv
    rw [valid.odd i inside]
    simp only [nonzeroSupport, Finset.erase_empty, Finset.map_empty, oddSyndrome, powerSum, Finset.sum_empty]
    exact toField_zero.symm

/-- The ID set represented by one row of a fixed modulo-routed shape. -/
def routedIds (buckets bucket : Nat) (ids : Finset U64) : Finset U64 :=
  ids.filter (fun id => id.val % buckets = bucket)

theorem routed_symmDiff (buckets bucket : Nat) (left right : Finset U64) :
    routedIds buckets bucket (left ∆ right) =
      routedIds buckets bucket left ∆ routedIds buckets bucket right := by
  ext id
  simp only [routedIds, Finset.mem_filter, Finset.mem_symmDiff]
  by_cases route : id.val % buckets = bucket <;> simp [route]

theorem routed_zero (buckets bucket : Nat) (ids : Finset U64) :
    0#u64 ∈ routedIds buckets bucket ids ↔ bucket = 0 ∧ 0#u64 ∈ ids := by
  simp only [routedIds, Finset.mem_filter, show (0#u64).val = 0 from rfl, Nat.zero_mod]
  constructor
  · rintro ⟨present, zero⟩
    exact ⟨zero.symm, present⟩
  · rintro ⟨zero, present⟩
    exact ⟨present, zero.symm⟩

/-- A per-row decoder result denoting the difference of the two routed
sets assembles into the exact whole-sketch difference in bucket order.
Original source routing returns the row index of every recovered ID. -/
theorem native_routed_rows_lift {F : Type} (field : bulksketch.field.BinaryField F)
    (shape : bulksketch.sketch.shape.SketchShape F) (left right : Finset U64)
    (rows : Nat → List U64) (positive : 0 < shape.capacities.length)
    (each : ∀ bucket < shape.capacities.length, (rows bucket).Nodup ∧
      (rows bucket).toFinset = routedIds shape.capacities.length bucket left ∆
        routedIds shape.capacities.length bucket right) :
    let output := (List.range shape.capacities.length).flatMap rows
    output.Nodup ∧ output.toFinset = left ∆ right ∧
      ∀ bucket < shape.capacities.length, ∀ id ∈ rows bucket, ∃ routed : Usize,
        bulksketch.sketch.shape.SketchShape.bucket_for field shape id = .ok routed ∧
        routed.val = bucket := by
  let n := shape.capacities.length
  have rowMem (bucket : Nat) (inside : bucket < n) (id : U64) :
      id ∈ rows bucket ↔ id ∈ left ∆ right ∧ id.val % n = bucket := by
    rw [← List.mem_toFinset, (each bucket inside).2, ← routed_symmDiff]
    exact Finset.mem_filter
  refine ⟨List.nodup_flatMap.mpr ⟨fun bucket member => (each bucket (List.mem_range.mp member)).1, ?_⟩, ?_, ?_⟩
  · apply (List.pairwise_iff_getElem).2
    intro i j iBound jBound earlier
    have xBound : (List.range n)[i] < n := List.mem_range.mp (List.getElem_mem iBound)
    have yBound : (List.range n)[j] < n := List.mem_range.mp (List.getElem_mem jBound)
    apply List.disjoint_left.mpr
    intro id inFirst inSecond
    have first := ((rowMem _ xBound id).mp inFirst).2
    have second := ((rowMem _ yBound id).mp inSecond).2
    rw [List.getElem_range] at first second
    omega
  · apply Finset.ext
    intro id
    simp only [List.mem_toFinset, List.mem_flatMap, List.mem_range]
    constructor
    · rintro ⟨bucket, inside, member⟩
      exact ((rowMem bucket inside id).mp member).1
    · intro member
      have inside : id.val % n < n := Nat.mod_lt _ positive
      exact ⟨_, inside, (rowMem _ inside id).mpr ⟨member, rfl⟩⟩
  · intro bucket inside id member
    obtain ⟨routed, actual, value, _⟩ :=
      CandidateNormalization.native_candidate_bucket field shape id positive
    exact ⟨routed, actual, value.trans ((rowMem bucket inside id).mp member).2⟩

#print axioms portable_sketch_xor
#print axioms decoded_ids_exact_at_budget
#print axioms equal_words_and_flag_iff_empty
#print axioms native_routed_rows_lift

end BulksketchBridge.PortableSketchBoundary
