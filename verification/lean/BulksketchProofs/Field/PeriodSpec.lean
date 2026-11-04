import BulksketchProofs.Field.SpreadSpec

/-!
Additive Std-only meaning for the existing portable square/repeated-square
word model. These definitions do not change the earlier frozen bridge model.
No irreducibility or field-period assumption occurs in the statements.
-/

namespace BulksketchProofs.Field.Period

/-- Exact complete-word polynomial square followed by native-modulus reduction. -/
def squareWord (input : BitVec 64) : BitVec 64 :=
  reduceFold64 (spread64 input) (spread64 (input >>> 32))

/-- Unmodded natural-count iteration of the square map. -/
def iterateSquare : Nat → BitVec 64 → BitVec 64
  | 0, input => input
  | count + 1, input => squareWord (iterateSquare count input)

/-- One polynomial-basis vector, with its sole coefficient at `index`. -/
def basisWord (index : Fin 64) : BitVec 64 :=
  (1 : BitVec 64) <<< index.val

def BasisCertificate : Prop :=
  ∀ index : Fin 64, iterateSquare 64 (basisWord index) = basisWord index

def SixtyFourSquaresIdentity : Prop :=
  ∀ input : BitVec 64, iterateSquare 64 input = input

def IterationModulo64 : Prop :=
  ∀ (count : Nat) (input : BitVec 64),
    iterateSquare (count % 64) input = iterateSquare count input

end BulksketchProofs.Field.Period
