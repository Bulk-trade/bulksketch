import BulksketchBridge.Algebra.WordSpec
import Mathlib.FieldTheory.Finite.Trace

/-!
# Trace of the actual polynomial quotient

The carrier is Mathlib's `AdjoinRoot` of the exact irreducible degree-64
polynomial.  These dimension and trace identities use that quotient and its
ordinary `Algebra.trace`, rather than introducing a second trace operation.
-/

namespace BulksketchBridge.Algebra.Gf64

noncomputable instance fieldFiniteDimensional : Module.Finite (ZMod 2) Field :=
  modulus_monic.finite_adjoinRoot

noncomputable instance fieldFinite : Finite Field :=
  Module.finite_of_finite (ZMod 2)

/-- The exact quotient has degree 64 over the two-element field. -/
theorem field_finrank : Module.finrank (ZMod 2) Field = 64 := by
  simpa only [AdjoinRoot.powerBasis_dim, modulus_natDegree] using
    (AdjoinRoot.powerBasis modulus_irreducible.ne_zero).finrank

/-- The quotient contains exactly one field value for each 64-bit word. -/
theorem field_natCard : Nat.card Field = 2 ^ 64 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, field_finrank]

/-- Mathlib's algebra trace is the sum of all 64 binary conjugates. -/
theorem algebra_trace_conjugate_sum (input : Field) :
    algebraMap (ZMod 2) Field (Algebra.trace (ZMod 2) Field input) =
      ∑ index ∈ Finset.range 64, input ^ (2 ^ index) := by
  simpa only [field_finrank, Nat.card_zmod] using
    FiniteField.algebraMap_trace_eq_sum_pow (ZMod 2) Field input

end BulksketchBridge.Algebra.Gf64
