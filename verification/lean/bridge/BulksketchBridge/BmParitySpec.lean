import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.CharP.Two

namespace BulksketchBridge.BmParity

open Polynomial

variable {K : Type} [CommRing K]

/-- Multiplication by the index on coefficients. In characteristic two it
keeps exactly the odd powers. -/
noncomputable def euler (p : K[X]) : K[X] := X * derivative p

noncomputable def residual (connection syndromes : K[X]) : K[X] :=
  connection * syndromes + euler connection

noncomputable def squareDefect (syndromes : K[X]) : K[X] :=
  euler syndromes + syndromes + syndromes ^ 2

/-- If every preceding residual coefficient is zero, the skipped
even-power discrepancy vanishes for any row obeying the square relation
through that power. A finite polynomial suffices. -/
def SkippedDiscrepancy : Prop :=
  ∀ {K : Type} [CommRing K] [CharP K 2]
    (connection syndromes : K[X]) (m : Nat)
    (_even : m % 2 = 0) (_zeroConstant : syndromes.coeff 0 = 0)
    (_squared : ∀ i, 2 * i ≤ m → syndromes.coeff (2 * i) = (syndromes.coeff i) ^ 2)
    (_earlier : ∀ j < m, (residual connection syndromes).coeff j = 0),
    (connection * syndromes).coeff m = 0

/-- A nonzero update cancels the residual at the current power and
preserves every earlier zero. The anchor condition accounts for the
Euler contribution from the shift, including the bootstrap step. -/
def UpdateResidualPrefix : Prop :=
  ∀ {K : Type} [CommRing K] [CharP K 2]
    (row previous syndromes : K[X])
    (m shift anchor : Nat) (b delta : K) (_aligned : m = anchor + shift)
    (_earlier : ∀ i < m, (residual row syndromes).coeff i = 0)
    (_current : (residual row syndromes).coeff m = delta)
    (_anchorEarlier : ∀ i < anchor,
      (residual previous syndromes + C (shift : K) * previous).coeff i = 0)
    (_anchorValue : (residual previous syndromes + C (shift : K) * previous).coeff anchor = b),
    ∀ i ≤ m, (residual (C b * row + C delta * (X ^ shift * previous)) syndromes).coeff i = 0

end BulksketchBridge.BmParity
