import BulksketchBridge.BmParitySpec
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic.Ring

namespace BulksketchBridge.BmParity

open Polynomial
open scoped BigOperators

variable {K : Type} [CommRing K] [CharP K 2]

omit [CharP K 2] in
theorem coeff_euler (p : K[X]) (n : Nat) :
    (euler p).coeff n = p.coeff n * (n : K) := by
  cases n <;> simp [euler, coeff_X_mul, coeff_derivative]

theorem euler_idempotent (p : K[X]) : euler (euler p) = euler p := by
  ext n
  simp only [coeff_euler]
  rw [CharP.cast_eq_mod K 2 n]
  have residues : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases residues with h | h <;> simp [h]

omit [CharP K 2] in
theorem euler_product (p q : K[X]) :
    euler (p * q) = euler p * q + p * euler q := by
  simp only [euler, derivative_mul, mul_add]
  ring

omit [CharP K 2] in
theorem euler_add (p q : K[X]) : euler (p + q) = euler p + euler q := by
  simp [euler, derivative_add, mul_add]

/-- The binary power-sum relation makes the first nonzero residual
coefficient occur at an odd power. This identity retains the explicit
defect term so it can be used for finite syndrome buffers. -/
theorem residual_identity (connection syndromes : K[X]) :
    euler (residual connection syndromes) + residual connection syndromes +
      syndromes * residual connection syndromes = connection * squareDefect syndromes := by
  simp only [residual, squareDefect, euler_add, euler_product, euler_idempotent]
  calc
    _ = connection * (euler syndromes + syndromes + syndromes ^ 2) +
          (euler connection * syndromes + euler connection * syndromes) +
          (euler connection + euler connection) := by ring
    _ = _ := by simp only [CharTwo.add_self_eq_zero, add_zero]

omit [CharP K 2] in
private theorem coeff_mul_zero (p q : K[X]) (n : Nat)
    (zero : ∀ i j : Nat, i + j = n → p.coeff i * q.coeff j = 0) :
    (p * q).coeff n = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ij member
  exact zero ij.1 ij.2 (Finset.mem_antidiagonal.mp member)

theorem coeff_square_even (s : K[X]) (i : Nat) :
    (s ^ 2).coeff (2 * i) = (s.coeff i) ^ 2 := by
  have exp := congrArg (fun p : K[X] => p.coeff (2 * i)) (map_frobenius_expand s (p := 2))
  simpa [coeff_map, coeff_expand, frobenius_def, Nat.mul_comm 2 i] using exp.symm

theorem coeff_square_odd (s : K[X]) (n : Nat) (odd : n % 2 = 1) :
    (s ^ 2).coeff n = 0 := by
  have exp := congrArg (fun p : K[X] => p.coeff n) (map_frobenius_expand s (p := 2))
  have ndvd : ¬ 2 ∣ n := by omega
  simpa [coeff_map, coeff_expand, ndvd] using exp.symm

theorem reconstructed_defect_zero (s : K[X]) (m : Nat)
    (squared : ∀ i, 2 * i ≤ m → s.coeff (2 * i) = (s.coeff i) ^ 2)
    (j : Nat) (bounded : j ≤ m) : (squareDefect s).coeff j = 0 := by
  simp only [squareDefect, coeff_add, coeff_euler]
  rw [CharP.cast_eq_mod K 2 j]
  by_cases even : j % 2 = 0
  · obtain ⟨i, rfl⟩ := Nat.dvd_of_mod_eq_zero even
    rw [even, Nat.cast_zero, mul_zero, zero_add, coeff_square_even, ← squared i bounded,
      CharTwo.add_self_eq_zero]
  · have odd : j % 2 = 1 := by omega
    rw [odd, Nat.cast_one, mul_one, coeff_square_odd s j odd, add_zero, CharTwo.add_self_eq_zero]

theorem skipped_discrepancy : SkippedDiscrepancy := by
  intro K _ _ connection syndromes m even zeroConstant squared earlier
  have defect := coeff_mul_zero connection (squareDefect syndromes) m (by
    intro i j sum
    rw [reconstructed_defect_zero syndromes m squared j (by omega), mul_zero])
  have product := coeff_mul_zero syndromes (residual connection syndromes) m (by
    intro i j sum
    by_cases iz : i = 0
    · rw [iz, zeroConstant, zero_mul]
    · rw [earlier j (by omega), mul_zero])
  have eq := congrArg (fun p : K[X] => p.coeff m) (residual_identity connection syndromes)
  simp only [coeff_add, coeff_euler, CharP.cast_eq_mod K 2 m, even, Nat.cast_zero,
    mul_zero, zero_add, product, add_zero, defect] at eq
  simpa only [residual, coeff_add, coeff_euler, CharP.cast_eq_mod K 2 m, even,
    Nat.cast_zero, mul_zero, add_zero] using eq

omit [CharP K 2] in
theorem residual_shift (row syndromes : K[X]) (shift : Nat) :
    residual (X ^ shift * row) syndromes =
      X ^ shift * (residual row syndromes + C (shift : K) * row) := by
  have shiftEuler : euler (X ^ shift : K[X]) = C (shift : K) * X ^ shift := by
    ext i
    rw [coeff_euler, coeff_C_mul, coeff_X_pow]
    split_ifs with h
    · rw [h, one_mul, mul_one]
    · rw [zero_mul, mul_zero]
  simp only [residual, euler_product, shiftEuler]
  ring

omit [CharP K 2] in
theorem residual_scale_add (a b : K) (p q s : K[X]) :
    residual (C a * p + C b * q) s = C a * residual p s + C b * residual q s := by
  simp only [residual, euler_add, euler_product]
  simp only [euler, derivative_C, mul_zero, zero_mul, zero_add]
  ring

theorem update_residual_prefix : UpdateResidualPrefix := by
  intro K _ _ row previous syndromes m shift anchor b delta aligned earlier current anchorEarlier anchorValue i bounded
  rw [residual_scale_add, residual_shift, coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_pow_mul']
  by_cases currentIndex : i = m
  · subst i
    rw [current, ite_eq_left (by omega), show m - shift = anchor by omega, anchorValue,
      mul_comm delta b, CharTwo.add_self_eq_zero]
  · rw [earlier i (by omega), mul_zero, zero_add]
    split_ifs with h
    · rw [anchorEarlier (i - shift) (by omega), mul_zero]
    · rw [mul_zero]

omit [CharP K 2] in
theorem current_discrepancy (row syndromes : K[X]) (m : Nat) (degree : row.natDegree < m) :
    (residual row syndromes).coeff m = (row * syndromes).coeff m := by
  simp [residual, coeff_euler, coeff_eq_zero_of_natDegree_lt degree]

theorem regular_anchor (previous syndromes : K[X]) (shift anchor : Nat) (b : K)
    (evenShift : shift % 2 = 0)
    (earlier : ∀ i < anchor, (residual previous syndromes).coeff i = 0)
    (value : (residual previous syndromes).coeff anchor = b) :
    (∀ i < anchor, (residual previous syndromes + C (shift : K) * previous).coeff i = 0) ∧
    (residual previous syndromes + C (shift : K) * previous).coeff anchor = b := by
  have shiftCast : (shift : K) = 0 := by rw [CharP.cast_eq_mod K 2 shift, evenShift, Nat.cast_zero]
  simpa only [shiftCast, map_zero, zero_mul, add_zero] using And.intro earlier value

theorem bootstrap_anchor (syndromes : K[X]) (shift : Nat) (oddShift : shift % 2 = 1)
    (zeroConstant : syndromes.coeff 0 = 0) :
    (residual 1 syndromes + C (shift : K) * 1).coeff 0 = 1 := by
  rw [CharP.cast_eq_mod K 2 shift, oddShift]
  simp [residual, euler, zeroConstant]

end BulksketchBridge.BmParity
