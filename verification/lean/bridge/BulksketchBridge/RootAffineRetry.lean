import BulksketchBridge.RootAffineGuards
import BulksketchBridge.RootRunGcd

namespace BulksketchBridge.RootRun

open Aeneas.Std Polynomial Algebra.Gf64 AffineSubspaces AffineSubspaceAlgebra
open bulksketch.decode.roots bulksketch.decode.scratch

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

/-- A split simple factor of degree at least two cannot fit in a rank-zero coset. -/
theorem affine_rank_positive (factor : Polynomial Field) (base : Field) (basis : Slice U64)
    (rank : Nat) (degree : 2 ≤ factor.natDegree) (nonzero : factor ≠ 0)
    (split : factor.Splits) (simple : factor.roots.Nodup)
    (contains : ∀ point, factor.IsRoot point → point ∈ coset base (prefixDirections basis rank)) :
    0 < rank := by
  classical
  by_contra! zeroRank
  have rankZero : rank = 0 := by omega
  have subset : factor.roots.toFinset ⊆ {base} := by
    intro point member
    have root := (mem_roots nonzero).mp (Multiset.mem_toFinset.mp member)
    have inCoset : point ∈ coset base [] := by
      simpa only [rankZero, prefixDirections] using contains point root
    have total : point + base = 0 := inCoset
    have pointEq : point = base := by
      calc
        point = (point + base) + base := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
        _ = base := by rw [total, zero_add]
    simpa only [Finset.mem_singleton] using pointEq
  have card := Finset.card_le_card subset
  rw [Multiset.toFinset_card_of_nodup simple, ← split.natDegree_eq_card_roots, Finset.card_singleton] at card
  omega

private theorem gcd_root_iff (factor trace : Polynomial Field) (point : Field) :
    (gcd factor trace).IsRoot point ↔ factor.IsRoot point ∧ trace.IsRoot point := by
  simp only [← dvd_iff_isRoot, dvd_gcd_iff]

/-- On an original nonproper affine GCD outcome the rank strictly falls.
    A constant gcd selects the shifted child and a full-degree gcd keeps the
    existing base. Every factor root stays in the smaller coset. -/
def ActualAffineGcdRetry : Prop :=
  ∀ (roots : Roots) (buffers : FactorWork) (basis : Slice U64) (size : Usize)
    (factor trace : Polynomial Field),
    roots.affine = true → 0 < roots.affine_rank.val →
    factor.Monic → factor.natDegree = roots.degree.val →
    size.val = (gcd factor trace).natDegree + 1 →
    ¬ Proper roots size →
    basisAt buffers (roots.affine_rank.val - 1) = basis[roots.affine_rank.val - 1]! →
    (∀ point, factor.IsRoot point →
      point ∈ coset (toField roots.affine_base.bv) (prefixDirections basis roots.affine_rank.val)) →
    (∀ point, factor.IsRoot point → (trace.IsRoot point ↔
      point ∈ coset (toField roots.affine_base.bv) (prefixDirections basis (roots.affine_rank.val - 1)))) →
    let output := outcome roots buffers size
    output.1 = .Ok (.Ok .AffineSplit) ∧
    output.2.affine_rank.val = roots.affine_rank.val - 1 ∧
    ∀ point, factor.IsRoot point →
      point ∈ coset (toField output.2.affine_base.bv) (prefixDirections basis output.2.affine_rank.val)

theorem affine_gcd_retry : ActualAffineGcdRetry := by
  intro roots buffers basis size factor trace affine rankPositive monic factorDegree
    sizeExact notProper direction contains classifies
  have gcdNonzero : gcd factor trace ≠ 0 :=
    fun zero => monic.ne_zero ((gcd_eq_zero_iff factor trace).mp zero).1
  have gcdMonic := (Polynomial.normalize_eq_self_iff_monic gcdNonzero).mp (normalize_gcd factor trace)
  let rank := roots.affine_rank.val - 1
  have rankValue : (previousRank roots).val = rank := by
    change (BitVec.ofNat System.Platform.numBits rank).toNat = rank
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) roots.affine_rank.hBounds)
  have rankSucc : roots.affine_rank.val = rank + 1 := by omega
  let base := toField roots.affine_base.bv
  let step := toField basis[rank]!.bv
  let earlier := prefixDirections basis rank
  have splitPoint (point : Field) (root : factor.IsRoot point) :
      point ∈ coset base earlier ∨ point ∈ coset (base + step) earlier := by
    apply (coset_children base step point earlier).mp
    simpa only [rankSucc, prefixDirections, base, step, earlier] using contains point root
  have nonProper : ¬ (0 < size.val - 1 ∧ size.val - 1 < roots.degree.val) := notProper
  by_cases constant : size = 1#usize
  · have zero : (gcd factor trace).natDegree = 0 := by
      have sizeOne : size.val = 1 := by rw [constant]; rfl
      omega
    have baseWord :
        toField (roots.affine_base ^^^ basisAt buffers (previousRank roots).val).bv = base + step := by
      rw [rankValue]
      change toField (roots.affine_base.bv ^^^ (basisAt buffers rank).bv) = base + step
      rw [toField_xor, direction]
    have oneNotProper : ¬ (0 < (1#usize : Usize).val - 1 ∧ (1#usize : Usize).val - 1 < roots.degree.val) := by
      change ¬ (0 < 1 - 1 ∧ _)
      omega
    simp only [outcome, oneNotProper, ite_false, affine, ite_true, constant, rankValue]
    refine ⟨trivial, rfl, ?_⟩
    intro point root
    have baseEq := baseWord
    rw [rankValue] at baseEq
    rw [baseEq]
    rcases splitPoint point root with first | second
    · have vanish := (classifies point root).mpr first
      have gcdRoot := (gcd_root_iff factor trace point).mpr ⟨root, vanish⟩
      have member := (mem_roots gcdMonic.ne_zero).mpr gcdRoot
      have count := Multiset.card_pos_iff_exists_mem.mpr ⟨point, member⟩
      have bound := card_roots' (gcd factor trace)
      omega
    · exact second
  · have degreePositive : 0 < (gcd factor trace).natDegree := by
      by_contra! degreeZero
      apply constant
      apply UScalar.eq_of_val_eq
      change size.val = 1
      omega
    have fullDegree : factor.natDegree ≤ (gcd factor trace).natDegree := by omega
    have full : factor = gcd factor trace :=
      eq_of_monic_of_dvd_of_natDegree_le gcdMonic monic (gcd_dvd_left factor trace) fullDegree
    simp only [outcome, nonProper, ite_false, affine, ite_true, constant, rankValue]
    refine ⟨trivial, rfl, ?_⟩
    intro point root
    have gcdRoot : (gcd factor trace).IsRoot point := full ▸ root
    exact (classifies point root).mp ((gcd_root_iff factor trace point).mp gcdRoot).2

#print axioms affine_gcd_retry

end BulksketchBridge.RootRun
