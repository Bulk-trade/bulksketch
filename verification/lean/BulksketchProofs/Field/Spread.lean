import BulksketchProofs.Field.SpreadSpec

/-!
# Universal bit-level correctness of the native-shaped spread model

Proofs below enumerate only the 64 possible output indices. Every input word
remains universally quantified; this is not enumeration of 2^64 inputs.
Rust/Aeneas source refinement is not asserted by these model theorems.
-/

namespace BulksketchProofs.Field

/-- Exact bit coefficients of spread, for every 64-bit input word. -/
theorem spread64_bits (word : BitVec 64) (i : Nat) (hi : i < 64) :
    (spread64 word).getLsbD i =
      if i % 2 = 0 then word.getLsbD (i / 2) else false := by
  have indexCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega
  rcases indexCases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  -- Keep total Boolean getters: rewriting them to dependent `GetElem` creates
  -- nested bound-proof transports for underflowing shift indices. Avoiding
  -- those transports preserves the statement and keeps independent replay small.
  all_goals subst i; simp [spread64, -BitVec.getLsbD_eq_getElem]

/-- Every low input coefficient is placed at its even output position. -/
theorem spread64_even_bits (word : BitVec 64) (i : Nat) (hi : i < 32) :
    (spread64 word).getLsbD (2 * i) = word.getLsbD i := by
  rw [spread64_bits word (2 * i) (by omega)]
  simp

/-- Every odd output coefficient is zero. -/
theorem spread64_odd_bits (word : BitVec 64) (i : Nat) (hi : i < 32) :
    (spread64 word).getLsbD (2 * i + 1) = false := by
  rw [spread64_bits word (2 * i + 1) (by omega)]
  simp

/-- Agreement on only the low 32 bits is sufficient for equal spread outputs. -/
theorem spread64_low32_congr (left right : BitVec 64)
    (h : ∀ i, i < 32 → left.getLsbD i = right.getLsbD i) :
    spread64 left = spread64 right := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [spread64_bits left i hi, spread64_bits right i hi]
  split
  · exact h (i / 2) (by omega)
  · rfl

/-- High 32 input bits are irrelevant, exactly as the source's first mask intends. -/
theorem spread64_ignores_high32 (word : BitVec 64) :
    spread64 ((word.setWidth 32).setWidth 64) = spread64 word := by
  apply spread64_low32_congr
  intro i hi
  have h64 : i < 64 := by omega
  simp [hi, h64]

/-- Interleaving is a linear map on polynomial coefficients. -/
theorem spread64_xor (left right : BitVec 64) :
    spread64 (left ^^^ right) = spread64 left ^^^ spread64 right := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor]
  rw [spread64_bits (left ^^^ right) i hi,
    spread64_bits left i hi, spread64_bits right i hi]
  split <;> simp [*]

/-- Low-half coefficients of the raw low/high polynomial layout. -/
theorem join128_low_bits (low high : BitVec 64) (i : Nat) (hi : i < 64) :
    (join128 low high).getLsbD i = low.getLsbD i := by
  have h128 : i < 128 := by omega
  simp [join128, hi, h128]

/-- High-half coefficients of the raw low/high polynomial layout. -/
theorem join128_high_bits (low high : BitVec 64) (i : Nat) (hi : i < 64) :
    (join128 low high).getLsbD (64 + i) = high.getLsbD i := by
  have h128 : 64 + i < 128 := by omega
  simp [join128, hi, h128]

/-- Before reduction, squaring inserts a zero between every two input coefficients.
This universally characterizes all 128 output coefficients. -/
theorem rawSquare128_bits (word : BitVec 64) (i : Nat) (hi : i < 128) :
    (rawSquare128 word).getLsbD i =
      if i % 2 = 0 then word.getLsbD (i / 2) else false := by
  by_cases hlo : i < 64
  · rw [rawSquare128, join128_low_bits _ _ i hlo]
    exact spread64_bits word i hlo
  · have hpart : i - 64 < 64 := by omega
    have hindex : i = 64 + (i - 64) := by omega
    have hparity : (i - 64) % 2 = i % 2 := by omega
    have hhalf : 32 + (i - 64) / 2 = i / 2 := by omega
    calc
      (rawSquare128 word).getLsbD i =
          (rawSquare128 word).getLsbD (64 + (i - 64)) := congrArg _ hindex
      _ = (spread64 (word >>> 32)).getLsbD (i - 64) :=
        join128_high_bits _ _ _ hpart
      _ = if (i - 64) % 2 = 0 then
          (word >>> 32).getLsbD ((i - 64) / 2) else false :=
        spread64_bits _ _ hpart
      _ = if i % 2 = 0 then word.getLsbD (i / 2) else false := by
        simp only [BitVec.getLsbD_ushiftRight, hparity, hhalf]

/-- All 64 input bits survive as their even raw-square coefficients. -/
theorem rawSquare128_even_bits (word : BitVec 64) (i : Nat) (hi : i < 64) :
    (rawSquare128 word).getLsbD (2 * i) = word.getLsbD i := by
  rw [rawSquare128_bits word (2 * i) (by omega)]
  simp

/-- Every odd coefficient of the complete raw square is zero. -/
theorem rawSquare128_odd_bits (word : BitVec 64) (i : Nat) (hi : i < 64) :
    (rawSquare128 word).getLsbD (2 * i + 1) = false := by
  rw [rawSquare128_bits word (2 * i + 1) (by omega)]
  simp

/-- The raw square is XOR-linear before modular reduction. -/
theorem rawSquare128_xor (left right : BitVec 64) :
    rawSquare128 (left ^^^ right) = rawSquare128 left ^^^ rawSquare128 right := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor]
  rw [rawSquare128_bits (left ^^^ right) i hi,
    rawSquare128_bits left i hi, rawSquare128_bits right i hi]
  split <;> simp [*]

end BulksketchProofs.Field
