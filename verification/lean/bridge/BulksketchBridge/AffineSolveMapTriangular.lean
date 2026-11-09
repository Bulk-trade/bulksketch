import BulksketchBridge.AffineSolveMapSoundness
import BulksketchBridge.AffineEnumerationCoset

namespace BulksketchBridge.AffineSolveMap

open Aeneas.Std FrobeniusTables Algebra.Gf64

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

def PreimagesBelow (state : EliminationState) (width : Nat) : Prop :=
  ∀ i < 64, entry state.images i ≠ 0#u64 → (entry state.preimages i).val < 2 ^ width

def KernelTriangular (state : EliminationState) (width : Nat) : Prop :=
  ∀ row < state.rank.val, ∃ lead < width,
    2 ^ lead ≤ (entry state.kernel row).val ∧
    (entry state.kernel row).val < 2 ^ (lead + 1) ∧
    ∀ earlier < row, (entry state.kernel earlier).val < 2 ^ lead

private theorem basis_value (i : Nat) (active : i < 64) : (basisBit i).val = 2 ^ i := by
  change ((1 : BitVec 64) <<< i).toNat = _
  rw [BitVec.toNat_shiftLeft, show (1 : BitVec 64).toNat = 1 from rfl, Nat.shiftLeft_eq, Nat.one_mul]
  rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) active)]

private theorem xor_val (left right : U64) :
    (left ^^^ right).val = left.val ^^^ right.val := by
  change (left.bv ^^^ right.bv).toNat = _
  rw [BitVec.toNat_xor]
  rfl

private theorem xor_below {left right : U64} {width : Nat}
    (a : left.val < 2 ^ width) (b : right.val < 2 ^ width) :
    (left ^^^ right).val < 2 ^ width := by
  rw [xor_val]
  exact Nat.xor_lt_two_pow a b

private theorem xor_zero_word (word : U64) : word ^^^ 0#u64 = word := by
  apply U64.bv_eq_imp_eq
  change word.bv ^^^ (0 : BitVec 64) = word.bv
  exact BitVec.xor_zero

/-- Each cancellation changes the original input witness by an XOR of
preimages of already processed columns, all below the current input bit. -/
theorem reduced_witness_below {state : EliminationState} {original image reduced final : U64}
    (path : Reduced state.images state.preimages original image reduced final)
    (width : Nat) (prior : PreimagesBelow state width) :
    ∃ low : U64, low.val < 2 ^ width ∧ reduced = original ^^^ low := by
  induction path with
  | zero original | vacant original =>
    refine ⟨0#u64, ?_, (xor_zero_word original).symm⟩
    change 0 < 2 ^ width
    exact pow_pos (by decide) _
  | cancel original image _ _ active occupied _ ih =>
    obtain ⟨later, fits, result⟩ := ih
    have earlier := prior (pivot image) (pivot_lt_width image active) occupied
    refine ⟨entry state.preimages (pivot image) ^^^ later, xor_below earlier fits, ?_⟩
    rw [result]
    apply U64.bv_eq_imp_eq
    change (original.bv ^^^ (entry state.preimages (pivot image)).bv) ^^^ later.bv =
      original.bv ^^^ ((entry state.preimages (pivot image)).bv ^^^ later.bv)
    exact BitVec.xor_assoc ..

private theorem new_leading_bit (bit : Nat) (active : bit < 64) (low : U64) (fits : low.val < 2 ^ bit) :
    2 ^ bit ≤ (basisBit bit ^^^ low).val ∧ (basisBit bit ^^^ low).val < 2 ^ (bit + 1) := by
  rw [xor_val, basis_value bit active]
  have set : (2 ^ bit ^^^ low.val).testBit bit = true := by
    rw [Nat.testBit_xor, Nat.testBit_two_pow_self, Nat.testBit_lt_two_pow fits]
    rfl
  have width : 2 ^ bit < 2 ^ (bit + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
  exact ⟨Nat.ge_two_pow_of_testBit set, Nat.xor_lt_two_pow width (fits.trans width)⟩

private theorem trace_order {columns : Slice U64} {start stop : Nat} {before after : EliminationState}
    (trace : ColumnTrace columns start before stop after) : start ≤ stop := by
  induction trace <;> omega

/-- In the actual source sweep every recorded kernel witness has a new
leading bit, above all earlier recorded directions. -/
theorem elimination_triangular {columns : Slice U64} {start stop : Nat} {before after : EliminationState}
    (trace : ColumnTrace columns start before stop after)
    (stopBound : stop ≤ 64) (rankBound : before.rank.val ≤ start)
    (preimages : PreimagesBelow before start) (kernel : KernelTriangular before start) :
    PreimagesBelow after stop ∧ KernelTriangular after stop := by
  induction trace with
  | finished => exact ⟨preimages, kernel⟩
  | dependent index state reduced rank path increment stop output rest ih =>
    have indexBound : index < 64 := (trace_order rest).trans stopBound
    have writable : state.rank.val < (64#usize).val := by change state.rank.val < 64; omega
    obtain ⟨low, fits, result⟩ := reduced_witness_below path index preimages
    have ⟨lowBit, upperBit⟩ := new_leading_bit index indexBound low fits
    have wider : 2 ^ index ≤ 2 ^ (index + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    apply ih stopBound (by simp only; omega)
    · intro i inside present
      exact (preimages i inside present).trans_le wider
    · intro row active
      change row < rank.val at active
      change ∃ lead < index + 1,
        2 ^ lead ≤ (entry (state.kernel.set state.rank reduced) row).val ∧
        (entry (state.kernel.set state.rank reduced) row).val < 2 ^ (lead + 1) ∧
        ∀ earlier < row, (entry (state.kernel.set state.rank reduced) earlier).val < 2 ^ lead
      by_cases new : row = state.rank.val
      · subst row
        rw [entry_set_same _ _ _ writable, result]
        refine ⟨index, by omega, lowBit, upperBit, ?_⟩
        intro earlier prior
        rw [entry_set_other _ _ _ _ (by omega : state.rank.val ≠ earlier)]
        obtain ⟨lead, below, _, high, _⟩ := kernel earlier prior
        exact high.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
      · have old : row < state.rank.val := by omega
        obtain ⟨lead, below, lo, hi, earlier⟩ := kernel row old
        rw [entry_set_other _ _ _ _ (Ne.symm new)]
        refine ⟨lead, by omega, lo, hi, ?_⟩
        intro prior fits
        rw [entry_set_other _ _ _ _ (by omega : state.rank.val ≠ prior)]
        exact earlier prior fits
  | independent index state reduced final path present stop output rest ih =>
    have indexBound : index < 64 := (trace_order rest).trans stopBound
    obtain ⟨low, fits, result⟩ := reduced_witness_below path index preimages
    have ⟨_, upperBit⟩ := new_leading_bit index indexBound low fits
    have wider : 2 ^ index ≤ 2 ^ (index + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    apply ih stopBound (by simp only; omega)
    · intro i inside used
      change entry (inserted state.images final final) i ≠ 0#u64 at used
      change (entry (inserted state.preimages final reduced) i).val < 2 ^ (index + 1)
      simp only [inserted, present, ite_false] at used ⊢
      by_cases same : i = (pivotWord final).val
      · subst i
        rw [entry_set_same _ _ _ inside, result]
        exact upperBit
      · rw [entry_set_other _ _ _ _ (Ne.symm same)] at used ⊢
        exact (preimages i inside used).trans_le wider
    · intro i active
      obtain ⟨lead, below, lo, hi, earlier⟩ := kernel i active
      exact ⟨lead, by omega, lo, hi, earlier⟩


private def FieldBelow (width : Nat) (value : Field) : Prop :=
  (wordFieldEquiv.symm value).toNat < 2 ^ width

private theorem field_below_word (width : Nat) (word : U64) :
    FieldBelow width (toField word.bv) ↔ word.val < 2 ^ width := by
  unfold FieldBelow
  change (wordFieldEquiv.symm (wordFieldEquiv word.bv)).toNat < 2 ^ width ↔ _
  rw [Equiv.symm_apply_apply]
  rfl

private theorem field_below_add (width : Nat) (left right : Field)
    (a : FieldBelow width left) (b : FieldBelow width right) :
    FieldBelow width (left + right) := by
  let leftWord : U64 := ⟨wordFieldEquiv.symm left⟩
  let rightWord : U64 := ⟨wordFieldEquiv.symm right⟩
  have leftEq : toField leftWord.bv = left := wordFieldEquiv.apply_symm_apply left
  have rightEq : toField rightWord.bv = right := wordFieldEquiv.apply_symm_apply right
  have leftBelow : leftWord.val < 2 ^ width := a
  have rightBelow : rightWord.val < 2 ^ width := b
  rw [← leftEq, ← rightEq, ← toField_xor]
  exact (field_below_word width (leftWord ^^^ rightWord)).mpr (xor_below leftBelow rightBelow)

private theorem field_below_span (width : Nat) (basis : List Field)
    (words : ∀ value ∈ basis, FieldBelow width value) (value : Field)
    (member : value ∈ AffineSubspaceAlgebra.spanWords basis) : FieldBelow width value := by
  induction basis generalizing value with
  | nil =>
    simp only [AffineSubspaceAlgebra.spanWords, Set.mem_singleton_iff] at member
    subst value
    have zero : FieldBelow width (toField (0#u64).bv) :=
      (field_below_word width 0#u64).mpr (by change 0 < 2 ^ width; exact pow_pos (by decide) _)
    rwa [show toField (0#u64).bv = 0 from toField_zero] at zero
  | cons direction earlier ih =>
    have old : ∀ value ∈ earlier, FieldBelow width value := fun value inList =>
      words value (List.mem_cons_of_mem _ inList)
    simp only [AffineSubspaceAlgebra.spanWords, Set.mem_union, Set.mem_image] at member
    rcases member with direct | ⟨prior, direct, rfl⟩
    · exact ih old value direct
    · exact field_below_add width prior direction (ih old prior direct) (words direction (List.mem_cons_self ..))

private theorem direction_in_prefix (basis : Slice U64) (width : Nat) (value : Field)
    (member : value ∈ AffineSubspaces.prefixDirections basis width) :
    ∃ index < width, value = toField basis[index]!.bv := by
  induction width with
  | zero => simp [AffineSubspaces.prefixDirections] at member
  | succ width ih =>
    simp only [AffineSubspaces.prefixDirections, List.mem_cons] at member
    rcases member with rfl | tail
    · exact ⟨width, Nat.lt_succ_self _, rfl⟩
    · obtain ⟨i, inside, equal⟩ := ih tail
      exact ⟨i, inside.trans (Nat.lt_succ_self _), equal⟩

open DenseCoefficient RebuiltLfsr in
theorem kernel_prefix_independent (state : EliminationState) (width : Nat)
    (rankBound : state.rank.val ≤ 64) (triangular : KernelTriangular state width) :
    AffineEnumerate.IndependentDirections (prefixSlice state.kernel.to_slice state.rank.val) := by
  let kernel := prefixSlice state.kernel.to_slice state.rank.val
  have widthEq : kernel.length = state.rank.val := by
    change (prefixSlice state.kernel.to_slice state.rank.val).length = _
    rw [prefix_length, Array.length_to_slice, show (64#usize).val = 64 from rfl, Nat.min_eq_left rankBound]
  have wordAt (index : Nat) (inside : index < state.rank.val) : kernel[index]! = entry state.kernel index := by
    simp only [kernel, prefixSlice, Slice.getElem!_Nat_eq, Slice.from_val, Array.to_slice,
      List.getElem!_eq_getElem?_getD, List.getElem?_take_of_lt inside, entry]
  intro row active member
  change row < kernel.length at active
  rw [widthEq] at active
  obtain ⟨lead, _, lower, _, prior⟩ := triangular row active
  have older (value : Field) (present : value ∈ AffineSubspaces.prefixDirections kernel row) :
      FieldBelow lead value := by
    obtain ⟨index, earlier, equal⟩ := direction_in_prefix kernel row value present
    rw [equal, wordAt index (earlier.trans active), field_below_word]
    exact prior index earlier
  change toField kernel[row]!.bv ∈ AffineSubspaceAlgebra.spanWords (AffineSubspaces.prefixDirections kernel row) at member
  have tooSmall := field_below_span lead _ older _ member
  rw [wordAt row active, field_below_word] at tooSmall
  exact (Nat.not_lt_of_ge lower) tooSmall


open Aeneas DenseCoefficient bulksketch.backend.contract in
def ActualNativeKernelIndependent : Prop :=
  ∀ {K : Type} (field : bulksketch.field.BinaryField bulksketch.field.Gf64)
    (kernels : BulkKernels K bulksketch.field.Gf64),
    field.BITS = .ok 64#u32 → TimesXMod.ExactScaleXor kernels →
    ∀ (affine : Slice U64) (initial written : Columns) (base : U64) (rank : Usize),
      0 < affine.length → affine.length ≤ 65 →
      bulksketch.decode.affine.solve_map field kernels affine initial = .ok (some (base, rank), written) →
      rank.val ≤ 64 ∧ AffineEnumerate.IndependentDirections (prefixSlice written.to_slice rank.val)

theorem native_kernel_independent : ActualNativeKernelIndependent := by
  intro K field kernels bits scale affine initial written base rank positive width normal
  obtain ⟨_, _, output, reduced, final, _, _, trace, _, bounded, _, solved⟩ :=
    solve_map_gf64_refines field kernels bits scale affine initial positive width
  have emptyPreimages : PreimagesBelow (initialElimination initial) 0 := by
    intro i active present
    change entry (Array.repeat 64#usize 0#u64) i ≠ 0#u64 at present
    exact (present (entry_repeat _ _ _ active)).elim
  have emptyKernel : KernelTriangular (initialElimination initial) 0 := by
    intro row active
    change row < 0 at active
    omega
  have triangular := (elimination_triangular trace (Nat.le_refl _) (Nat.zero_le _) emptyPreimages emptyKernel).2
  have equal := Result.ok_injective (solved.symm.trans normal)
  by_cases zero : final = 0#u64
  · simp only [zero, ite_true] at equal
    have same := Option.some.inj (congrArg Prod.fst equal)
    have rankEq : output.rank = rank := congrArg Prod.snd same
    have writtenEq : output.kernel = written := congrArg Prod.snd equal
    rw [← rankEq, ← writtenEq]
    exact ⟨bounded, kernel_prefix_independent output 64 bounded triangular⟩
  · simp only [zero, ite_false] at equal
    have impossible : (none : Option (U64 × Usize)) = some (base, rank) := congrArg Prod.fst equal
    cases impossible


end BulksketchBridge.AffineSolveMap
