import BulksketchProofs.Field.PeriodSpec
import BulksketchProofs.Field.PeriodBasis
import BulksketchProofs.Field.Spread
import BulksketchProofs.Field.Reduction

namespace BulksketchProofs.Field.Period

/-- Sum exactly the selected low `count` polynomial basis coefficients. -/
def xorPrefix (input : BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | count + 1 => xorPrefix input count ^^^
      (if input.getLsbD count then (1 : BitVec 64) <<< count else 0)

private theorem one_shift_bit (count index : Nat) (hi : index < 64) :
    ((1 : BitVec 64) <<< count).getLsbD index = decide (index = count) := by
  simp only [BitVec.getLsbD_shiftLeft, hi, decide_true,
    Bool.true_and]
  by_cases before : index < count
  · simp [before, show index ≠ count by omega]
  · simp [before, show index - count = 0 ↔ index = count by omega]

theorem xorPrefix_bits (input : BitVec 64) (count index : Nat) (hi : index < 64) :
    (xorPrefix input count).getLsbD index =
      if index < count then input.getLsbD index else false := by
  induction count with
  | zero => simp [xorPrefix]
  | succ count ih =>
    rw [xorPrefix, BitVec.getLsbD_xor, ih]
    have contribution :
        (if input.getLsbD count then (1 : BitVec 64) <<< count else 0).getLsbD index =
          (input.getLsbD count && decide (index = count)) := by
      cases h : input.getLsbD count
      · change (0 : BitVec 64).getLsbD index = false
        exact BitVec.getLsbD_zero
      · change ((1 : BitVec 64) <<< count).getLsbD index = decide (index = count)
        exact one_shift_bit count index hi
    rw [contribution]
    by_cases same : index = count
    · subst index
      simp
    · simp only [same, decide_false, Bool.and_false, Bool.xor_false,
        show (index < count + 1) ↔ index < count by omega]

/-- Every complete word is the XOR sum of its 64 selected basis vectors. -/
theorem xorPrefix_complete (input : BitVec 64) : xorPrefix input 64 = input := by
  apply BitVec.eq_of_getLsbD_eq
  intro index hi
  rw [xorPrefix_bits input 64 index hi]
  simp [hi]

/-- Equality of zero/XOR-preserving word maps is determined by 64 basis images. -/
theorem xor_linear_basis_ext {width : Nat} (left right : BitVec 64 → BitVec width)
    (leftZero : left 0 = 0) (rightZero : right 0 = 0)
    (leftXor : ∀ a b, left (a ^^^ b) = left a ^^^ left b)
    (rightXor : ∀ a b, right (a ^^^ b) = right a ^^^ right b)
    (basis : ∀ index : Fin 64, left (basisWord index) = right (basisWord index)) :
    ∀ input, left input = right input := by
  intro input
  have agreePrefix : ∀ count, count ≤ 64 →
      left (xorPrefix input count) = right (xorPrefix input count) := by
    intro count
    induction count with
    | zero => simp only [xorPrefix, leftZero, rightZero, implies_true]
    | succ count ih =>
      intro hc
      rw [xorPrefix, leftXor, rightXor, ih (by omega)]
      cases h : input.getLsbD count
      · change right (xorPrefix input count) ^^^ left (0 : BitVec 64) =
          right (xorPrefix input count) ^^^ right (0 : BitVec 64)
        rw [leftZero, rightZero]
      · change right (xorPrefix input count) ^^^ left ((1 : BitVec 64) <<< count) =
          right (xorPrefix input count) ^^^ right ((1 : BitVec 64) <<< count)
        exact congrArg
          (fun word => right (xorPrefix input count) ^^^ word)
          (basis ⟨count, by omega⟩)
  rw [← xorPrefix_complete input]
  exact agreePrefix 64 (by decide)

/-- The native-shaped polynomial-square model is XOR-linear. -/
theorem squareWord_xor (left right : BitVec 64) :
    squareWord (left ^^^ right) = squareWord left ^^^ squareWord right := by
  simp only [squareWord, spread64_xor, BitVec.ushiftRight_xor_distrib,
    reduceFold64_xor]

theorem squareWord_zero : squareWord 0 = 0 := by
  have h := squareWord_xor 0 0
  simpa using h

theorem iterateSquare_xor (count : Nat) (left right : BitVec 64) :
    iterateSquare count (left ^^^ right) =
      iterateSquare count left ^^^ iterateSquare count right := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [iterateSquare, ih, squareWord_xor]

theorem iterateSquare_zero (count : Nat) : iterateSquare count 0 = 0 := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [iterateSquare, ih, squareWord_zero]

/-- Linearity lifts the checked 64-basis certificate to all 2^64 words. -/
theorem sixty_four_squares_identity : SixtyFourSquaresIdentity := by
  exact xor_linear_basis_ext (iterateSquare 64) (fun input => input)
    (iterateSquare_zero 64) rfl (iterateSquare_xor 64) (by intros; rfl)
    basis_certificate

/-- Concatenating iteration counts composes the same square map. -/
theorem iterateSquare_add (first second : Nat) (input : BitVec 64) :
    iterateSquare (first + second) input =
      iterateSquare second (iterateSquare first input) := by
  induction second with
  | zero => rfl
  | succ second ih =>
    change squareWord (iterateSquare (first + second) input) =
      squareWord (iterateSquare second (iterateSquare first input))
    rw [ih]

/-- An arbitrary natural number of squarings depends only on its residue64. -/
theorem iteration_modulo64 : IterationModulo64 := by
  intro count input
  induction count using Nat.strongRecOn with
  | ind count ih =>
    by_cases small : count < 64
    · rw [Nat.mod_eq_of_lt small]
    · have large : 64 ≤ count := by omega
      have smaller : count - 64 < count := by omega
      have remainder : (count - 64) % 64 = count % 64 := by omega
      have step : iterateSquare count input = iterateSquare (count - 64) input := by
        rw [← Nat.sub_add_cancel large, iterateSquare_add]
        exact sixty_four_squares_identity (iterateSquare (count - 64) input)
      rw [← remainder, ih (count - 64) smaller]
      exact step.symm

end BulksketchProofs.Field.Period
