import BulksketchBridge.RootPendingProduct

namespace BulksketchBridge.RootRun

open Algebra.Gf64 Polynomial

/-- The mathematical conditions on a represented active or pending
    factor. The degree is the native declared coefficient degree. -/
structure ValidFactor (factor : Polynomial Field) (degree : Nat) : Prop where
  monic : factor.Monic
  exactDegree : factor.natDegree = degree
  split : factor.Splits
  simple : factor.roots.Nodup
  nonzeroRoots : ∀ point, factor.IsRoot point → point ≠ 0

theorem valid_factor_of_monic_dvd (parent factor : Polynomial Field) (parentDegree degree : Nat)
    (valid : ValidFactor parent parentDegree) (monic : factor.Monic)
    (exactDegree : factor.natDegree = degree) (divides : factor ∣ parent) : ValidFactor factor degree := by
  obtain ⟨parentMonic, _, split, simple, nonzero⟩ := valid
  refine ⟨monic, exactDegree, split.of_dvd parentMonic.ne_zero divides,
    Multiset.nodup_of_le (Polynomial.roots.le_of_dvd parentMonic.ne_zero divides) simple, ?_⟩
  intro point root
  exact nonzero point ((dvd_iff_isRoot).mp ((dvd_iff_isRoot.mpr root).trans divides))

/-- Exact normalized division preserves the factor validity needed by
    the next native table, trace, or leaf stage on either child. -/
theorem valid_children (parent left right : Polynomial Field) (degree leftDegree rightDegree : Nat)
    (valid : ValidFactor parent degree) (product : parent = right * left)
    (leftMonic : left.Monic) (leftExact : left.natDegree = leftDegree)
    (degreeSum : leftDegree + rightDegree = degree) :
    ValidFactor left leftDegree ∧ ValidFactor right rightDegree := by
  have parentMonic : parent.Monic := valid.monic
  rw [product] at parentMonic
  have rightMonic := leftMonic.of_mul_monic_right parentMonic
  have degree := valid.exactDegree
  rw [product, natDegree_mul rightMonic.ne_zero leftMonic.ne_zero, leftExact] at degree
  have rightExact : right.natDegree = rightDegree := by omega
  exact ⟨valid_factor_of_monic_dvd parent left _ _ valid leftMonic leftExact ⟨right, product.trans (mul_comm ..)⟩,
    valid_factor_of_monic_dvd parent right _ _ valid rightMonic rightExact ⟨left, product⟩⟩

end BulksketchBridge.RootRun
