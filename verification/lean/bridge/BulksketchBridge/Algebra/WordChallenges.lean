import BulksketchBridge.Algebra.WordSpec

/-! Frozen mathematical endpoints for the native polynomial-basis representation.
These specifications quantify complete words; they neither assume a successful
native call nor postulate an operation-preservation fact. -/
namespace BulksketchBridge.Algebra.Gf64.WordChallenges

open Polynomial
open BulksketchProofs.Field

/-- Coefficients are exact for every word width and every natural index. -/
def ExactPolynomialCoefficients : Prop :=
  ∀ (width : Nat) (input : BitVec width) (index : Nat),
    (wordPolynomial input).coeff index = if input.getLsbD index then 1 else 0

/-- The word map covers precisely the entire Mathlib quotient field. -/
def BijectiveRepresentation : Prop := Function.Bijective toField

/-- Polynomial coefficient addition is word XOR, and both identities agree. -/
def AdditiveRepresentation : Prop :=
  toField 0 = 0 ∧ toField 1 = 1 ∧
    ∀ (left right : BitVec 64), toField (left ^^^ right) = toField left + toField right

/-- All 128 bits of a raw product are represented before taking its quotient class. -/
def CompleteRawProduct : Prop :=
  ∀ (left right : BitVec 64),
    wordPolynomial (clmul128 left right) = wordPolynomial left * wordPolynomial right

/-- Every 128-bit input reduces to its canonical representative in the quotient. -/
def ReductionRepresentation : Prop :=
  ∀ (low high : BitVec 64), toField (reduceFold64 low high) =
    AdjoinRoot.mk modulus (wordPolynomial (join128 low high))

/-- The native word multiplication agrees with Mathlib's field multiplication. -/
def MultiplicationRepresentation : Prop :=
  ∀ (left right : BitVec 64),
    toField (multiplyWord left right) = toField left * toField right

/-- The native word square agrees with the square of the quotient-field value. -/
def SquareRepresentation : Prop :=
  ∀ (input : BitVec 64), toField (Period.squareWord input) = toField input ^ 2

/-- Complete field laws for the native arithmetic word model. -/
def ArithmeticFieldLaws : Prop :=
  ∀ (a b c : BitVec 64),
    multiplyWord a b = multiplyWord b a ∧
    multiplyWord (multiplyWord a b) c = multiplyWord a (multiplyWord b c) ∧
    multiplyWord a 1 = a ∧ multiplyWord 1 a = a ∧
    multiplyWord a 0 = 0 ∧ multiplyWord 0 a = 0 ∧
    multiplyWord a (b ^^^ c) = multiplyWord a b ^^^ multiplyWord a c ∧
    multiplyWord (a ^^^ b) c = multiplyWord a c ^^^ multiplyWord b c ∧
    Period.squareWord a = multiplyWord a a

end BulksketchBridge.Algebra.Gf64.WordChallenges
