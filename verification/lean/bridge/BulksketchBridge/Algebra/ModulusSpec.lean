import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.ZMod.Basic

/-!
# Exact binary polynomial used by native GF64 arithmetic

This is a mathematical specification over `Polynomial (ZMod 2)`. The native
bitvector-to-polynomial representation bridge is a separate obligation. In
particular, defining this polynomial does not assert irreducibility or identify
the quotient with a field.
-/

namespace BulksketchBridge.Algebra.Gf64

open Polynomial

/-- The monic degree-64 polynomial `X^64 + X^4 + X^3 + X + 1`. -/
noncomputable def modulus : Polynomial (ZMod 2) := X ^ 64 + X ^ 4 + X ^ 3 + X + 1

end BulksketchBridge.Algebra.Gf64
