import Arithmetic.AffineSolveMapGenerated
import BulksketchBridge.FrobeniusTablesSupport

namespace BulksketchBridge.AffineSolveMap

open Aeneas Aeneas.Std Result ControlFlow
open bulksketch.decode.affine
open FrobeniusTables (entry read_normal update_normal entry_set_same entry_set_other)

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

abbrev Columns := Array U64 64#usize

def pivot (word : U64) : Nat := word.bv.ctz.toNat

def pivotWord (word : U64) : Usize :=
  UScalar.cast .Usize (⟨word.bv.ctz.setWidth 32⟩ : U32)

private theorem cast_ctz (word : U64) :
    UScalar.cast .Usize (⟨word.bv.ctz.setWidth 32⟩ : U32) = pivotWord word := rfl

theorem pivot_le_width (word : U64) : pivot word ≤ 64 := trailingZeroCount_le_width word.bv

theorem pivot_word_val (word : U64) : (pivotWord word).val = pivot word := by
  have bound := pivot_le_width word
  have count : (⟨word.bv.ctz.setWidth 32⟩ : U32).val = pivot word := by
    change (word.bv.ctz.setWidth 32).toNat = pivot word
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (by change pivot word < 2 ^ 32; omega)
  rw [pivotWord, UScalar.cast_val_eq, count]
  apply Nat.mod_eq_of_lt
  change pivot word < 2 ^ System.Platform.numBits
  rcases System.Platform.numBits_eq with platform | platform <;> rw [platform] <;> omega

theorem pivot_set (word : U64) (nonzero : word ≠ 0#u64) :
    word.bv.getLsbD (pivot word) = true := by
  apply BitVec.getLsbD_true_ctz_of_ne_zero
  intro zero
  apply nonzero
  exact U64.bv_eq_imp_eq _ _ zero

theorem pivot_lt_width (word : U64) (nonzero : word ≠ 0#u64) : pivot word < 64 := by
  by_contra! bad
  have absent := BitVec.getLsbD_of_ge word.bv (pivot word) bad
  rw [pivot_set word nonzero] at absent
  contradiction

private theorem pivot_zero : pivot 0#u64 = 64 := by
  change (0 : BitVec 64).ctz.toNat = 64
  have zeroCount : (0 : BitVec 64).ctz = BitVec.ofNat 64 64 := by
    simp only [BitVec.ctz]
    apply BitVec.clz_eq_iff_eq_zero.mpr
    simp
  rw [zeroCount]
  rfl

def Pivots (images : Columns) : Prop :=
  ∀ i, i < 64 → entry images i ≠ 0#u64 → pivot (entry images i) = i

theorem empty_pivots : Pivots (Array.repeat 64#usize 0#u64) := by
  intro i inside present
  rw [FrobeniusTables.entry_repeat _ _ _ inside] at present
  contradiction

private theorem insert_preserves (images : Columns) (image : U64)
    (valid : Pivots images) :
    Pivots (images.set (pivotWord image) image) := by
  intro i inside hasWord
  by_cases same : i = (pivotWord image).val
  · subst i
    rw [entry_set_same _ _ _ inside, pivot_word_val]
  · rw [entry_set_other _ _ _ _ (Ne.symm same)] at hasWord ⊢
    exact valid i inside hasWord

private theorem pivot_advances (left right : U64) (leftPresent : left ≠ 0#u64)
    (rightPresent : right ≠ 0#u64) (samePivot : pivot right = pivot left) :
    pivot left < pivot (left ^^^ right) := by
  by_cases gone : left ^^^ right = 0#u64
  · rw [gone, pivot_zero]
    exact pivot_lt_width left leftPresent
  · by_contra! noAdvance
    have set := pivot_set (left ^^^ right) gone
    let i := pivot (left ^^^ right)
    change (left.bv ^^^ right.bv).getLsbD i = true at set
    rw [BitVec.getLsbD_xor] at set
    by_cases lower : i < pivot left
    · have earlier : i < pivot right := by omega
      rw [BitVec.getLsbD_false_of_lt_ctz (x := left.bv) lower,
        BitVec.getLsbD_false_of_lt_ctz (x := right.bv) earlier] at set
      simp at set
    · have atPivot : i = pivot left := by omega
      have rightSet := pivot_set right rightPresent
      rw [samePivot] at rightSet
      rw [atPivot, pivot_set left leftPresent, rightSet] at set
      simp at set

/-- A witnessed reduction path through occupied pivots, ending either
at zero or at the first vacant pivot. -/
inductive Reduced (images preimages : Columns) : U64 → U64 → U64 → U64 → Prop
  | zero (original : U64) :
      Reduced images preimages original 0#u64 original 0#u64
  | vacant (original image : U64) (active : image ≠ 0#u64)
      (empty : entry images (pivot image) = 0#u64) :
      Reduced images preimages original image original image
  | cancel (original image reduced final : U64) (active : image ≠ 0#u64)
      (occupied : entry images (pivot image) ≠ 0#u64)
      (next : Reduced images preimages (original ^^^ entry preimages (pivot image))
        (image ^^^ entry images (pivot image)) reduced final) :
      Reduced images preimages original image reduced final

theorem reduced_terminal {images preimages : Columns} {original image reduced final : U64}
    (path : Reduced images preimages original image reduced final) :
    final = 0#u64 ∨ entry images (pivot final) = 0#u64 := by
  induction path with
  | zero => exact Or.inl rfl
  | vacant _ _ _ empty => exact Or.inr empty
  | cancel _ _ _ _ _ _ _ tail => exact tail

def inserted (images : Columns) (image : U64) (value : U64) : Columns :=
  if image = 0#u64 then images else images.set (pivotWord image) value

/-- Every output slot is determined. Existing rows remain unchanged; only
the vacant pivot receives a new image and its matching preimage. -/
theorem eliminate_column (images preimages : Columns) (original image : U64)
    (valid : Pivots images) :
    ∃ reduced final,
      solve_map_loop1_loop0 images preimages original image =
        .ok (inserted images final final, inserted preimages final reduced, reduced, final) ∧
      Reduced images preimages original image reduced final ∧
      Pivots (inserted images final final) := by
  suffices ∀ remaining original image, 64 - pivot image = remaining →
    ∃ reduced final,
      solve_map_loop1_loop0 images preimages original image =
        .ok (inserted images final final, inserted preimages final reduced, reduced, final) ∧
      Reduced images preimages original image reduced final ∧
      Pivots (inserted images final final) by
    exact this (64 - pivot image) original image rfl
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro original image fuel
    by_cases zero : image = 0#u64
    · subst image
      refine ⟨original, 0#u64, ?_, .zero original, ?_⟩
      · rw [solve_map_loop1_loop0, loop]
        simp only [solve_map_loop1_loop0.body, bne_self_eq_false, Bool.false_eq_true,
          ite_false, bind_ok, inserted, ite_true]
      · simpa only [inserted, ite_true] using valid
    · have active : (image != 0#u64) = true := by simp [zero]
      have inside := pivot_lt_width image zero
      have indexBound : (pivotWord image).val < (64#usize).val := by rwa [pivot_word_val]
      have imageRead := read_normal images (pivotWord image) indexBound
      have witnessRead := read_normal preimages (pivotWord image) indexBound
      have trailing : bulksketch.AffineSolveMapRuntime.trailingZeros image =
          .ok (⟨image.bv.ctz.setWidth 32⟩ : U32) := rfl
      by_cases empty : entry images (pivot image) = 0#u64
      · refine ⟨original, image, ?_, .vacant original image zero empty, ?_⟩
        · rw [solve_map_loop1_loop0, loop]
          simp only [solve_map_loop1_loop0.body, active, ite_true, trailing, bind_ok, lift]

          simp only [cast_ctz, imageRead, pivot_word_val, empty, bind_ok, ite_true,
            update_normal images (pivotWord image) image indexBound,
            update_normal preimages (pivotWord image) original indexBound,
            inserted, zero, ite_false]
        · simpa only [inserted, zero, ite_false] using insert_preserves images image valid
      · have later := pivot_advances image (entry images (pivot image)) zero empty
          (valid _ inside empty)
        have measure : 64 - pivot (image ^^^ entry images (pivot image)) < remaining := by omega
        obtain ⟨reduced, final, exactLoop, path, finalValid⟩ :=
          ih _ measure (original ^^^ entry preimages (pivot image))
            (image ^^^ entry images (pivot image)) rfl
        refine ⟨reduced, final, ?_, .cancel original image reduced final zero empty path, finalValid⟩
        rw [solve_map_loop1_loop0, loop]
        simp only [solve_map_loop1_loop0.body, active, ite_true, trailing, bind_ok, lift]

        simp only [cast_ctz, imageRead, pivot_word_val, empty, bind_ok, ite_false, witnessRead]
        simpa only [solve_map_loop1_loop0, solve_map_loop1_loop0.body, lift, bind_ok] using exactLoop

/-- The target scan follows the same witnessed reduction path. A nonzero
residual with no pivot is exactly the source's None return. -/
theorem reduce_target (images preimages : Columns) (rank : Usize)
    (solution target reduced final : U64)
    (path : Reduced images preimages solution target reduced final) :
    solve_map_loop2 images preimages rank target solution =
      .ok (if final = 0#u64 then some (reduced, rank) else none) := by
  induction path with
  | zero original =>
    rw [solve_map_loop2, loop]
    simp only [solve_map_loop2.body, bne_self_eq_false, Bool.false_eq_true, ite_false,
      ite_true, bind_ok]
  | vacant original image nonzero empty =>
    have active : (image != 0#u64) = true := by simp [nonzero]
    have indexBound : (pivotWord image).val < (64#usize).val := by
      rw [pivot_word_val]
      exact pivot_lt_width image nonzero
    have trailing : bulksketch.AffineSolveMapRuntime.trailingZeros image =
      .ok (⟨image.bv.ctz.setWidth 32⟩ : U32) := rfl
    rw [solve_map_loop2, loop]
    simp only [solve_map_loop2.body, active, trailing, bind_ok, lift, ite_true]

    simp only [cast_ctz, read_normal images (pivotWord image) indexBound, pivot_word_val,
      empty, ite_true, bind_ok, nonzero, ite_false]
  | cancel original image reduced final nonzero occupied _ tail =>
    have active : (image != 0#u64) = true := by simp [nonzero]
    have indexBound : (pivotWord image).val < (64#usize).val := by
      rw [pivot_word_val]
      exact pivot_lt_width image nonzero
    have trailing : bulksketch.AffineSolveMapRuntime.trailingZeros image =
      .ok (⟨image.bv.ctz.setWidth 32⟩ : U32) := rfl
    rw [solve_map_loop2, loop]
    simp only [solve_map_loop2.body, active, trailing, bind_ok, lift, ite_true]

    simp only [cast_ctz, read_normal images (pivotWord image) indexBound, pivot_word_val,
      occupied, ite_false, bind_ok, read_normal preimages (pivotWord image) indexBound]
    simpa only [solve_map_loop2, solve_map_loop2.body, lift, bind_ok] using tail

#print axioms eliminate_column
#print axioms reduce_target

end BulksketchBridge.AffineSolveMap
