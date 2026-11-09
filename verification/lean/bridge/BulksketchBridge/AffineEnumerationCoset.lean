import BulksketchBridge.AffineGrayFill
import BulksketchBridge.AffineSubspacesAnnihilators

namespace BulksketchBridge.AffineEnumerate

open Aeneas.Std Algebra.Gf64 AffineSubspaceAlgebra AffineSubspaces
open scoped BigOperators

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

/-- Prefix independence matches the invariant needed by binary elimination.
    Each new direction lies outside the span of the earlier directions. -/
def IndependentDirections (basis : Slice U64) : Prop :=
  ∀ i < basis.length, toField basis[i]!.bv ∉ spanWords (prefixDirections basis i)

section Coordinates

variable {F : Type} [Field F]

private def directions (words : Nat → F) : Nat → List F
  | 0 => []
  | rank + 1 => words rank :: directions words rank

private noncomputable def prefixMask (words : Nat → F) (rank mask : Nat) : F :=
  ∑ bit ∈ Finset.range rank, if mask.testBit bit then words bit else 0

private theorem prefix_low (words : Nat → F) (rank mask : Nat) (low : mask < 2 ^ rank) :
    prefixMask words (rank + 1) mask = prefixMask words rank mask := by
  simp only [prefixMask, Finset.sum_range_succ, Nat.testBit_lt_two_pow low, Bool.false_eq_true,
    ite_false, add_zero]

private theorem prefix_high (words : Nat → F) (rank mask : Nat) (low : mask < 2 ^ rank) :
    prefixMask words (rank + 1) (2 ^ rank + mask) =
      prefixMask words rank mask + words rank := by
  simp only [prefixMask, Finset.sum_range_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow low,
    Bool.not_false, ite_true]
  congr 1
  apply Finset.sum_congr rfl
  intro bit member
  rw [Nat.testBit_two_pow_add_gt (Finset.mem_range.mp member)]

private theorem prefix_membership (words : Nat → F) (rank : Nat) (point : F) :
    point ∈ spanWords (directions words rank) ↔
      ∃ mask, mask < 2 ^ rank ∧ prefixMask words rank mask = point := by
  induction rank generalizing point with
  | zero =>
    simp only [pow_zero, prefixMask, Finset.range_zero,
      Finset.sum_empty]
    constructor
    · intro zero
      exact ⟨0, by decide, zero.symm⟩
    · rintro ⟨_, _, zero⟩
      exact zero.symm
  | succ rank ih =>
    change point ∈ spanWords (words rank :: directions words rank) ↔ _
    simp only [spanWords, Set.mem_union, Set.mem_image, pow_succ]
    constructor
    · rintro (old | ⟨earlier, old, rfl⟩)
      · obtain ⟨mask, low, represents⟩ := (ih point).mp old
        exact ⟨mask, by omega, (prefix_low words rank mask low).trans represents⟩
      · obtain ⟨mask, low, represents⟩ := (ih earlier).mp old
        refine ⟨2 ^ rank + mask, by omega, ?_⟩
        rw [prefix_high words rank mask low, represents]
    · rintro ⟨mask, bounded, represents⟩
      by_cases low : mask < 2 ^ rank
      · exact Or.inl ((ih point).mpr ⟨mask, low, (prefix_low words rank mask low).symm.trans represents⟩)
      · let remainder := mask - 2 ^ rank
        have fits : remainder < 2 ^ rank := by unfold remainder; omega
        have high : mask = 2 ^ rank + remainder := by unfold remainder; omega
        refine Or.inr ⟨prefixMask words rank remainder, (ih _).mpr ⟨remainder, fits, rfl⟩, ?_⟩
        rw [high, prefix_high words rank remainder fits] at represents
        exact represents

variable [CharP F 2]

private theorem prefix_unique (words : Nat → F) (rank : Nat)
    (independent : ∀ i < rank, words i ∉ spanWords (directions words i)) {left right : Nat}
    (leftBound : left < 2 ^ rank) (rightBound : right < 2 ^ rank)
    (same : prefixMask words rank left = prefixMask words rank right) : left = right := by
  induction rank generalizing left right with
  | zero => simp only [pow_zero] at leftBound rightBound; omega
  | succ rank ih =>
    simp only [pow_succ] at leftBound rightBound
    have lower : ∀ i < rank, words i ∉ spanWords (directions words i) :=
      fun i active => independent i (by omega)
    have fresh := independent rank (by omega)
    have disjoint := children_disjoint (0 : F) (words rank) (directions words rank) fresh
    have lowMember (mask : Nat) (bound : mask < 2 ^ rank) :
        prefixMask words rank mask ∈ coset (0 : F) (directions words rank) := by
      change prefixMask words rank mask + 0 ∈ spanWords (directions words rank)
      rw [add_zero]
      exact (prefix_membership words rank _).mpr ⟨mask, bound, rfl⟩
    have highMember (mask : Nat) (bound : mask < 2 ^ rank) :
        prefixMask words rank mask + words rank ∈
          coset (0 + words rank) (directions words rank) := by
      change (prefixMask words rank mask + words rank) + (0 + words rank) ∈
        spanWords (directions words rank)
      rw [zero_add, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      exact (prefix_membership words rank _).mpr ⟨mask, bound, rfl⟩
    by_cases leftLow : left < 2 ^ rank
    · rw [prefix_low words rank left leftLow] at same
      by_cases rightLow : right < 2 ^ rank
      · rw [prefix_low words rank right rightLow] at same
        exact ih lower leftLow rightLow same
      · let remainder := right - 2 ^ rank
        have bound : remainder < 2 ^ rank := by unfold remainder; omega
        have high : right = 2 ^ rank + remainder := by unfold remainder; omega
        rw [high, prefix_high words rank remainder bound] at same
        exact (Set.disjoint_left.mp disjoint (lowMember left leftLow) (same.symm ▸ highMember remainder bound)).elim
    · let leftRest := left - 2 ^ rank
      have leftFits : leftRest < 2 ^ rank := by unfold leftRest; omega
      have leftHigh : left = 2 ^ rank + leftRest := by unfold leftRest; omega
      rw [leftHigh, prefix_high words rank leftRest leftFits] at same
      by_cases rightLow : right < 2 ^ rank
      · rw [prefix_low words rank right rightLow] at same
        exact (Set.disjoint_left.mp disjoint (lowMember right rightLow) (same ▸ highMember leftRest leftFits)).elim
      · let rightRest := right - 2 ^ rank
        have rightFits : rightRest < 2 ^ rank := by unfold rightRest; omega
        have rightHigh : right = 2 ^ rank + rightRest := by unfold rightRest; omega
        rw [rightHigh, prefix_high words rank rightRest rightFits] at same
        exact leftHigh.trans ((congrArg (2 ^ rank + ·)
          (ih lower leftFits rightFits (add_right_cancel same))).trans rightHigh.symm)

end Coordinates

private theorem directions_eq (basis : Slice U64) (rank : Nat) :
    directions (fun bit => toField basis[bit]!.bv) rank = prefixDirections basis rank := by
  induction rank with
  | zero => rfl
  | succ rank ih => simp only [directions, prefixDirections, ih]

theorem gray_coset_membership (basis : Slice U64) (base point : Field) :
    point ∈ coset base (prefixDirections basis basis.length) ↔
      ∃ index, index < 2 ^ basis.length ∧ grayPointValue basis base index = point := by
  change point + base ∈ spanWords (prefixDirections basis basis.length) ↔ _
  rw [← directions_eq basis basis.length, prefix_membership]
  constructor
  · rintro ⟨mask, bounded, represented⟩
    obtain ⟨index, coordinate⟩ := (gray_mask_permutation basis.length).2 ⟨mask, bounded⟩
    have maskEq : grayMask index.val = mask := congrArg Fin.val coordinate
    refine ⟨index.val, index.isLt, ?_⟩
    change base + prefixMask (fun bit => toField basis[bit]!.bv) basis.length (grayMask index.val) = point
    rw [maskEq, represented, add_comm base, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · rintro ⟨index, bounded, represented⟩
    refine ⟨grayMask index, gray_mask_bound index basis.length bounded, ?_⟩
    change base + prefixMask (fun bit => toField basis[bit]!.bv) basis.length (grayMask index) = point at represented
    rw [← represented, add_comm base, add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem gray_points_distinct (basis : Slice U64) (base : Field) (independent : IndependentDirections basis)
    {left right : Nat} (leftBound : left < 2 ^ basis.length) (rightBound : right < 2 ^ basis.length)
    (same : grayPointValue basis base left = grayPointValue basis base right) : left = right := by
  apply gray_mask_injective
  apply prefix_unique (fun bit => toField basis[bit]!.bv) basis.length
  · intro i active
    rw [directions_eq]
    exact independent i active
  · exact gray_mask_bound left _ leftBound
  · exact gray_mask_bound right _ rightBound
  · exact add_left_cancel same

end BulksketchBridge.AffineEnumerate
