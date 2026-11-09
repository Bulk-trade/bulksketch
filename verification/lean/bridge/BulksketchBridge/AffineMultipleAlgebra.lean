import BulksketchBridge.AffineSubspacesPolynomial
import BulksketchBridge.DenseReducerAlgebra
import BulksketchBridge.Algebra.InversePower
import BulksketchBridge.Algebra.Trace
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Squarefree.Basic

namespace BulksketchBridge.AffineMultiple

open Aeneas.Std Polynomial Algebra.Gf64 AffineSubspaces DenseReducerAlgebra SliceKernels
open scoped BigOperators

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

noncomputable def witnessPolynomial (constant : U64) (linear : Slice U64) : Polynomial Field :=
  C (toField constant.bv) + rowPolynomial linear

/-- The relation maintained by the paired elimination row and witness
    gives divisibility when the row reduces to zero. -/
theorem witness_divides_of_zero (modulus : Slice U64) (constant : U64) (linear : Slice U64)
    (relation : residue modulus (C (toField constant.bv)) +
      ∑ i ∈ Finset.range linear.length,
        residue modulus (C (toField linear[i]!.bv)) * residueX modulus ^ (2 ^ i) = 0) :
    slicePolynomial modulus ∣ witnessPolynomial constant linear := by
  apply (AdjoinRoot.mk_eq_zero (f := slicePolynomial modulus)).mp
  simpa only [witnessPolynomial, rowPolynomial, map_add, map_sum, map_mul, map_pow, AdjoinRoot.mk_X] using relation

theorem witness_derivative (constant : U64) (linear : Slice U64) (hasX : 0 < linear.length) :
    derivative (witnessPolynomial constant linear) = C (toField linear[(0 : Nat)]!.bv) := by
  rw [witnessPolynomial, derivative_add, derivative_C, zero_add, rowPolynomial, derivative_sum]
  rw [Finset.sum_eq_single 0]
  · simpa only [pow_zero, pow_one] using derivative_C_mul_X (toField linear[(0 : Nat)]!.bv)
  · intro index _ nonzero
    have even : 2 ∣ 2 ^ index := by
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
      exact ⟨2 ^ i, by rw [pow_succ, Nat.mul_comm]⟩
    have castZero : ((2 ^ index : Nat) : Field) = 0 := (CharP.cast_eq_zero_iff Field 2 _).mpr even
    rw [derivative_C_mul_X_pow, castZero, mul_zero, map_zero, zero_mul]
  · intro absent
    exact (absent (Finset.mem_range.mpr hasX)).elim

/-- If a repeated nonunit factor divides the input, any represented
    affine multiple has zero linear coefficient. -/
theorem repeated_factor_forces_zero_X (modulus : Slice U64) (constant : U64) (linear : Slice U64)
    (hasX : 0 < linear.length) (factor : Polynomial Field) (nonunit : ¬IsUnit factor)
    (repeated : factor ^ 2 ∣ slicePolynomial modulus)
    (multiple : slicePolynomial modulus ∣ witnessPolynomial constant linear) :
    linear[(0 : Nat)]! = 0#u64 := by
  obtain ⟨other, decomposition⟩ := repeated.trans multiple
  have derivativeDvd : factor ∣ derivative (witnessPolynomial constant linear) := by
    rw [decomposition, pow_two, derivative_mul, derivative_mul]
    exact dvd_add
      (dvd_mul_of_dvd_left (dvd_add (dvd_mul_left factor (derivative factor))
        (dvd_mul_right factor (derivative factor))) other)
      (dvd_mul_of_dvd_left (dvd_mul_right factor factor) (derivative other))
  rw [witness_derivative constant linear hasX] at derivativeDvd
  by_contra notZero
  have fieldNonzero : toField linear[(0 : Nat)]!.bv ≠ 0 := by
    intro zero
    apply notZero
    apply U64.bv_eq_imp_eq
    exact toField_injective (zero.trans toField_zero.symm)
  exact nonunit (isUnit_of_dvd_unit derivativeDvd (isUnit_C.mpr (isUnit_iff_ne_zero.mpr fieldNonzero)))

def squareRootWord (word : U64) : U64 :=
  ⟨BulksketchProofs.Field.Period.iterateSquare 63 word.bv⟩

theorem square_root_word (word : U64) :
    toField (squareRootWord word).bv ^ 2 = toField word.bv := by
  change toField (BulksketchProofs.Field.Period.iterateSquare 63 word.bv) ^ 2 = _
  rw [toField_iterateSquare, ← pow_mul]
  exact field_power_period (toField word.bv)

private def squareRootTail (linear : Slice U64) : Slice U64 :=
  Slice.from ((linear.val.drop 1).map squareRootWord) (by
    rw [List.length_map]
    exact (List.drop_length_is_le _ _).trans linear.length_ineq)

private theorem root_tail_length (linear : Slice U64) : (squareRootTail linear).length = linear.length - 1 := by
  simp only [squareRootTail, Slice.length, Slice.from_val, List.length_map, List.length_drop]

private theorem root_tail_word (linear : Slice U64) (index : Nat) (active : index < linear.length - 1) :
    (squareRootTail linear)[index]! = squareRootWord linear[index + 1]! := by
  simp only [squareRootTail, Slice.getElem!_Nat_eq, Slice.from_val]
  have inside : index < ((linear.val.drop 1).map squareRootWord).length := by
    rw [List.length_map, List.length_drop]
    change index < linear.length - 1
    exact active
  have source : 1 + index < linear.val.length := by
    change 1 + index < linear.length
    omega
  rw [← List.Inhabited_getElem_eq_getElem! _ _ inside, List.getElem_map, List.getElem_drop]
  rw [List.Inhabited_getElem_eq_getElem! _ _ source, Nat.add_comm 1 index]

/-- A represented affine multiple with zero linear coefficient is the
    square of a represented affine polynomial with one fewer column. -/
theorem witness_square_root (constant : U64) (linear : Slice U64) (hasX : 0 < linear.length)
    (zeroX : linear[(0 : Nat)]! = 0#u64) :
    witnessPolynomial (squareRootWord constant) (squareRootTail linear) ^ 2 =
      witnessPolynomial constant linear := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold witnessPolynomial
  rw [add_pow_char (p := 2), ← map_pow, square_root_word]
  congr 1
  unfold rowPolynomial
  rw [sum_pow_char (p := 2), root_tail_length,
    show linear.length = (linear.length - 1) + 1 by omega, Finset.sum_range_succ']
  have zero : toField (0#u64).bv = 0 := toField_zero
  simp only [zeroX, zero, map_zero, zero_mul, add_zero]
  rw [show linear.length - 1 + 1 - 1 = linear.length - 1 by omega]
  apply Finset.sum_congr rfl
  intro index member
  have active := Finset.mem_range.mp member
  rw [mul_pow, ← map_pow, root_tail_word linear index active, square_root_word, ← pow_mul, pow_succ (2 : Nat)]

/-- A least positive-degree affine multiple of a squarefree modulus
    has a nonzero linear coefficient. A square root would otherwise
    produce a smaller nonzero affine multiple. -/
theorem squarefree_least_multiple_has_X (modulus : Slice U64) (constant : U64) (linear : Slice U64)
    (hasX : 0 < linear.length)
    (positiveDegree : 0 < (slicePolynomial modulus).natDegree)
    (squarefree : Squarefree (slicePolynomial modulus))
    (nonzero : witnessPolynomial constant linear ≠ 0)
    (multiple : slicePolynomial modulus ∣ witnessPolynomial constant linear)
    (least : ∀ otherConstant otherLinear,
      witnessPolynomial otherConstant otherLinear ≠ 0 →
      slicePolynomial modulus ∣ witnessPolynomial otherConstant otherLinear →
      (witnessPolynomial constant linear).natDegree ≤
        (witnessPolynomial otherConstant otherLinear).natDegree) :
    linear[(0 : Nat)]! ≠ 0#u64 := by
  intro zero
  let root := witnessPolynomial (squareRootWord constant) (squareRootTail linear)
  have square : root ^ 2 = witnessPolynomial constant linear := witness_square_root constant linear hasX zero
  have rootNonzero : root ≠ 0 := by
    intro empty
    rw [empty, zero_pow (by decide)] at square
    exact nonzero square.symm
  have rootDivides : slicePolynomial modulus ∣ root :=
    (squarefree.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp (square.symm ▸ multiple)
  have rootPositive : 0 < root.natDegree := positiveDegree.trans_le (natDegree_le_of_dvd rootDivides rootNonzero)
  have minimal := least (squareRootWord constant) (squareRootTail linear) rootNonzero rootDivides
  change (witnessPolynomial constant linear).natDegree ≤ root.natDegree at minimal
  rw [← square, natDegree_pow] at minimal
  omega


end BulksketchBridge.AffineMultiple
