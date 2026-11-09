import BulksketchBridge.RootTraversalInvariant
import BulksketchBridge.RootReborrow

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 Polynomial SliceKernels DenseCoefficient
open bulksketch.decode.roots bulksketch.decode.scratch

theorem traversal_degree_budget (locator : Polynomial Field) (roots : Roots)
    (workspace : RowWorkspace) (capacity budget : Nat)
    (invariant : RootTraversalInvariant locator roots workspace capacity budget) :
    roots.degree.val ≤ budget := by
  have mass := invariant.mass
  have bounded := invariant.degreeBudget
  unfold factorDegreeMass at mass
  omega

theorem traversal_monic_word (locator : Polynomial Field) (roots : Roots)
    (workspace : RowWorkspace) (capacity budget : Nat)
    (invariant : RootTraversalInvariant locator roots workspace capacity budget)
    (minimum : 2 ≤ roots.degree.val) :
    (buffersFor roots workspace).modulus[roots.degree.val]! = 1#u64 := by
  have bound := traversal_degree_budget locator roots workspace capacity budget invariant
  have modWidth := (gcd_buffers_of_budget roots workspace capacity budget invariant.buffers minimum bound).2.1
  obtain ⟨monic, exactDegree, _, _, _⟩ := invariant.active (by omega)
  have coefficient : (slicePolynomial (buffersFor roots workspace).modulus).coeff roots.degree.val = 1 := by
    change (activeFactor roots workspace).coeff roots.degree.val = 1
    rw [← exactDegree, ← Polynomial.leadingCoeff]
    exact monic
  rw [slicePolynomial_coeff, ite_eq_left (by omega)] at coefficient
  apply U64.bv_eq_imp_eq
  exact toField_injective (coefficient.trans toField_one.symm)

theorem traversal_modulus_normal (locator : Polynomial Field) (roots : Roots)
    (workspace : RowWorkspace) (capacity budget : Nat)
    (invariant : RootTraversalInvariant locator roots workspace capacity budget)
    (minimum : 2 ≤ roots.degree.val) : DenseGcd.Normal (buffersFor roots workspace).modulus := by
  intro _
  have bound := traversal_degree_budget locator roots workspace capacity budget invariant
  rw [(gcd_buffers_of_budget roots workspace capacity budget invariant.buffers minimum bound).2.1,
    Nat.add_sub_cancel, traversal_monic_word locator roots workspace capacity budget invariant minimum]
  decide

end BulksketchBridge.RootRun
