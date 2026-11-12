import BulksketchBridge.Algebra.WordSpec

/-! Sparse support uniqueness for the GF64 polynomial basis. The first
stored word is the power-one syndrome. The zero element has a separate
membership channel and contributes no positive power syndrome. -/

namespace BulksketchBridge.Reconciliation

open Algebra.Gf64
open scoped BigOperators

noncomputable def powerSum {K : Type*} [Semiring K] (roots : Finset K)
    (power : Nat) : K :=
  ∑ root ∈ roots, root ^ power

noncomputable def oddSyndrome {K : Type*} [Semiring K] (roots : Finset K)
    (index : Nat) : K :=
  powerSum roots (2 * index + 1)

noncomputable def wordPowerSum (roots : Finset (BitVec 64)) (power : Nat) : Field :=
  ∑ root ∈ roots, toField root ^ power

noncomputable def wordOddSyndrome (roots : Finset (BitVec 64)) (index : Nat) : Field :=
  wordPowerSum roots (2 * index + 1)

/-- The first `capacity` odd syndromes determine all positive powers through
`2 * capacity`, including the last even power. -/
def GF64OddSyndromesDeterminePositivePowers : Prop :=
  ∀ (capacity : Nat) (left right : Finset (BitVec 64)),
    (∀ index, index < capacity → wordOddSyndrome left index = wordOddSyndrome right index) →
    ∀ power, 0 < power → power ≤ 2 * capacity →
      wordPowerSum left power = wordPowerSum right power

/-- At most one nonzero support of size at most `capacity` matches a checked
row of `capacity` odd syndromes. Finsets represent distinct support elements. -/
def GF64OddSyndromesIdentifySparseSupport : Prop :=
  ∀ (capacity : Nat) (left right : Finset (BitVec 64)),
    left.card ≤ capacity → right.card ≤ capacity →
    (0 : BitVec 64) ∉ left → (0 : BitVec 64) ∉ right →
    (∀ index, index < capacity → wordOddSyndrome left index = wordOddSyndrome right index) →
    left = right

end BulksketchBridge.Reconciliation
