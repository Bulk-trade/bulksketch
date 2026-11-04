module
public import Aeneas
@[expose] public section

/-!
Concrete value model for the Rust standard library's general usize.trailing_zeros.
Rust's uint macro forwards to the cttz intrinsic. Zero returns the target width;
nonzero values return the least set-bit index. The value-level specification and
bounds below are kernel-checked. Correspondence to Rust std/intrinsic lowering
and machine execution remains the explicit runtime/ISA trust boundary.
-/
namespace Aeneas.Std

@[rust_fun "core::num::{usize}::trailing_zeros"]
def core.num.Usize.trailing_zeros (word : Usize) : Result U32 :=
  .ok ⟨word.bv.ctz.setWidth 32⟩

/-- A trailing-zero count never exceeds the input's bitwidth, including zero. -/
theorem trailingZeroCount_le_width (word : BitVec width) :
    word.ctz.toNat ≤ width := by
  have bound := BitVec.clz_le (x := word.reverse)
  change word.ctz.toNat ≤ (BitVec.ofNat width width).toNat at bound
  exact Nat.le_trans bound (Nat.mod_le _ _)

/-- The model returns normally and preserves the complete natural zero count. -/
theorem usize_trailing_zeros_spec (word : Usize) :
    ∃ count : U32,
      core.num.Usize.trailing_zeros word = .ok count ∧
      count.val = word.bv.ctz.toNat ∧ count.val ≤ System.Platform.numBits := by
  have bound := trailingZeroCount_le_width word.bv
  have widthBound := System.Platform.numBits_le
  have fits : word.bv.ctz.toNat < 2 ^ 32 := by omega
  refine ⟨⟨word.bv.ctz.setWidth 32⟩, rfl, ?_, ?_⟩
  · change (word.bv.ctz.setWidth 32).toNat = word.bv.ctz.toNat
    simp only [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt fits
  · change (word.bv.ctz.setWidth 32).toNat ≤ System.Platform.numBits
    simpa only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt fits] using bound

/-- The general primitive has Rust's defined zero behavior on either target width. -/
theorem usize_trailing_zeros_zero :
    ∃ count : U32,
      core.num.Usize.trailing_zeros 0#usize = .ok count ∧
      count.val = System.Platform.numBits := by
  obtain ⟨count, normal, exactCount, _⟩ := usize_trailing_zeros_spec 0#usize
  refine ⟨count, normal, ?_⟩
  rw [exactCount]
  change (0 : BitVec System.Platform.numBits).ctz.toNat = System.Platform.numBits
  have zeroCount : (0 : BitVec System.Platform.numBits).ctz =
      BitVec.ofNat System.Platform.numBits System.Platform.numBits := by
    simp only [BitVec.ctz]
    apply BitVec.clz_eq_iff_eq_zero.mpr
    simp
  rw [zeroCount]
  simp only [BitVec.toNat_ofNat, Nat.mod_two_pow_self]

/-- All lower bits are zero; on nonzero input the returned position is set. -/
theorem usize_trailing_zeros_least_set_bit (word : Usize) :
    ∃ count : U32,
      core.num.Usize.trailing_zeros word = .ok count ∧
      count.val ≤ System.Platform.numBits ∧
      (∀ index, index < count.val → word.bv.getLsbD index = false) ∧
      (word.bv ≠ 0 → word.bv.getLsbD count.val = true) := by
  obtain ⟨count, normal, exactCount, bound⟩ := usize_trailing_zeros_spec word
  refine ⟨count, normal, bound, ?_, ?_⟩
  · intro index earlier
    rw [exactCount] at earlier
    exact BitVec.getLsbD_false_of_lt_ctz earlier
  · intro nonzero
    rw [exactCount]
    exact BitVec.getLsbD_true_ctz_of_ne_zero nonzero

/-- Equal nonzero natural values have the same least set-bit position even
when represented at different widths. The zero case deliberately stays separate. -/
theorem trailingZeroCount_eq_of_toNat_eq
    {left : BitVec leftWidth} {right : BitVec rightWidth}
    (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0)
    (sameValue : left.toNat = right.toNat) :
    left.ctz.toNat = right.ctz.toNat := by
  have sameBits (index : Nat) : left.getLsbD index = right.getLsbD index := by
    simp only [BitVec.getLsbD, sameValue]
  apply Nat.le_antisymm
  · by_contra denied
    have earlier : right.ctz.toNat < left.ctz.toNat := Nat.lt_of_not_ge denied
    have zeroBit := BitVec.getLsbD_false_of_lt_ctz (x := left) earlier
    rw [sameBits] at zeroBit
    have setBit := BitVec.getLsbD_true_ctz_of_ne_zero rightNonzero
    rw [setBit] at zeroBit
    contradiction
  · by_contra denied
    have earlier : left.ctz.toNat < right.ctz.toNat := Nat.lt_of_not_ge denied
    have zeroBit := BitVec.getLsbD_false_of_lt_ctz (x := right) earlier
    rw [← sameBits] at zeroBit
    have setBit := BitVec.getLsbD_true_ctz_of_ne_zero leftNonzero
    rw [setBit] at zeroBit
    contradiction

/-- The table caller's 1..15 range specializes the general primitive to the
same four-bit count, proving the U128 shift bound without replacing the model. -/
theorem usize_trailing_zeros_nibble (word : Usize)
    (positive : 1 ≤ word.val) (below16 : word.val < 16) :
    ∃ count : U32,
      core.num.Usize.trailing_zeros word = .ok count ∧
      count.val = (BitVec.ofNat 4 word.val).ctz.toNat ∧ count.val < 4 := by
  have sameValue : word.bv.toNat = (BitVec.ofNat 4 word.val).toNat := by
    change word.val = word.val % 16
    exact (Nat.mod_eq_of_lt below16).symm
  have wordNonzero : word.bv ≠ 0 := by
    intro zero
    have valueZero : word.val = 0 := by
      change word.bv.toNat = 0
      rw [zero]
      rfl
    omega
  have nibbleNonzero : (BitVec.ofNat 4 word.val) ≠ 0 := by
    intro zero
    have valueZero : word.val = 0 := by
      change word.bv.toNat = 0
      rw [sameValue, zero]
      rfl
    omega
  have sameCount := trailingZeroCount_eq_of_toNat_eq wordNonzero nibbleNonzero sameValue
  have nibbleBound := (BitVec.ctz_lt_iff_ne_zero (x := BitVec.ofNat 4 word.val)).mpr nibbleNonzero
  change (BitVec.ofNat 4 word.val).ctz.toNat < 4 at nibbleBound
  obtain ⟨count, normal, exactCount, _⟩ := usize_trailing_zeros_spec word
  refine ⟨count, normal, exactCount.trans sameCount, ?_⟩
  rw [exactCount, sameCount]
  exact nibbleBound

end Aeneas.Std
