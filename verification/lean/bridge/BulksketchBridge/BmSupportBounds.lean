import BulksketchBridge.BmResidualInvariant
import BulksketchBridge.BmReciprocalMeaning
import BulksketchBridge.ReconciliationLocator
import Mathlib.Algebra.Polynomial.Reverse

namespace BulksketchBridge.BmSupportBounds

open Aeneas.Std Polynomial Algebra.Gf64 BmSyndromePolynomials BmParity
open scoped BigOperators

set_option maxRecDepth 4096

section DegreeBound

variable {K : Type} [CommRing K]

private theorem euler_degree (p : K[X]) : (euler p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i beyond
  rw [coeff_euler, coeff_eq_zero_of_natDegree_lt beyond, zero_mul]

private theorem coeff_mul_first (left right : K[X]) (power : Nat)
    (earlier : ∀ i < power, right.coeff i = 0) :
    (left * right).coeff power = left.coeff 0 * right.coeff power := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_eq_single 0]
  · rw [Nat.sub_zero]
  · intro i member nonzero
    have bound := Finset.mem_range.mp member
    rw [earlier (power - i) (by omega), mul_zero]
  · intro missing
    exact (missing (Finset.mem_range.mpr (by omega))).elim

private theorem coeff_mul_prefix_zero (left right : K[X]) (power : Nat)
    (zero : ∀ i ≤ power, right.coeff i = 0) :
    (left * right).coeff power = 0 := by
  rw [coeff_mul_first left right power (fun i less => zero i (Nat.le_of_lt less)),
    zero power (Nat.le_refl _), mul_zero]

/-- A reference connection fitting the observed prefix bounds the first
nonzero discrepancy. Multiplying both residuals by the opposite rows
eliminates the common syndrome polynomial. -/
theorem discrepancy_degree_bound (row reference syndromes : K[X]) (power : Nat)
    (referenceUnit : reference.coeff 0 = 1)
    (referenceFits : ∀ i ≤ power, (residual reference syndromes).coeff i = 0)
    (earlier : ∀ i < power, (residual row syndromes).coeff i = 0)
    (nonzero : (residual row syndromes).coeff power ≠ 0) :
    power ≤ row.natDegree + reference.natDegree := by
  have identity :
      reference * residual row syndromes - row * residual reference syndromes =
      reference * euler row - row * euler reference := by
    unfold residual
    ring
  have coefficient := congrArg (fun p : K[X] => p.coeff power) identity
  simp only [coeff_sub, coeff_mul_first reference _ power earlier, referenceUnit, one_mul,
    coeff_mul_prefix_zero row _ power referenceFits, sub_zero] at coefficient
  have degree :
      (reference * euler row - row * euler reference).natDegree ≤ row.natDegree + reference.natDegree := by
    apply (natDegree_sub_le _ _).trans
    have left : (reference * euler row).natDegree ≤ reference.natDegree + (euler row).natDegree :=
      natDegree_mul_le
    have right : (row * euler reference).natDegree ≤ row.natDegree + (euler reference).natDegree :=
      natDegree_mul_le
    have rowEuler := euler_degree row
    have refEuler := euler_degree reference
    exact max_le (by omega) (by omega)
  by_contra! beyond
  rw [coefficient] at nonzero
  -- The identity says that the nonzero residual is a coefficient beyond
  -- the degree of the difference of the two Euler products.
  have beyondDifference : (reference * euler row - row * euler reference).natDegree < power := by omega
  exact nonzero (by simpa only [coeff_sub] using coeff_eq_zero_of_natDegree_lt beyondDifference)

end DegreeBound

noncomputable def supportConnection (roots : Finset Field) : Polynomial Field :=
  ∏ root ∈ roots, (1 - C root * X)

private noncomputable def singleSums (root : Field) (observed : Nat) : Polynomial Field :=
  (∑ n ∈ Finset.range (observed + 1), (C root * X) ^ n) - 1

noncomputable def truncatedPowerSums (roots : Finset Field) (observed : Nat) : Polynomial Field :=
  ∑ root ∈ roots, singleSums root observed

theorem support_constant (roots : Finset Field) : (supportConnection roots).coeff 0 = 1 := by
  change (constantCoeff (supportConnection roots)) = 1
  simp [supportConnection]

theorem support_degree (roots : Finset Field) : (supportConnection roots).natDegree ≤ roots.card := by
  unfold supportConnection
  refine (natDegree_prod_le _ _).trans ?_
  calc
    _ ≤ ∑ _ ∈ roots, 1 := by
      apply Finset.sum_le_sum
      intro root _
      have factor := natDegree_sub_le (1 : Polynomial Field) (C root * X)
      have product : (C root * (X : Polynomial Field)).natDegree ≤ (C root).natDegree + (X : Polynomial Field).natDegree :=
        natDegree_mul_le
      simp only [natDegree_one, natDegree_C, natDegree_X, zero_add] at factor product
      omega
    _ = _ := by simp

private theorem factor_residual (root : Field) (observed : Nat) :
    residual (1 - C root * X) (singleSums root observed) = -(C root * X) ^ (observed + 1) := by
  have eulerFactor : euler (1 - C root * X) = -(C root * X) := by
    simp only [euler, derivative_sub, derivative_one, derivative_C_mul, derivative_X, mul_one, zero_sub, mul_neg]
    ring
  unfold residual singleSums
  rw [eulerFactor]
  calc
    _ = -((∑ n ∈ Finset.range (observed + 1), (C root * X) ^ n) * (C root * X - 1)) - 1 := by ring
    _ = _ := by rw [geom_sum_mul]; ring

private theorem factor_fits (root : Field) (observed power : Nat) (within : power ≤ observed) :
    (residual (1 - C root * X) (singleSums root observed)).coeff power = 0 := by
  rw [factor_residual, coeff_neg, mul_pow, ← map_pow, coeff_C_mul_X_pow,
    ite_eq_right (by omega), neg_zero]

private theorem residual_product (left right leftSums rightSums : Polynomial Field) :
    residual (left * right) (leftSums + rightSums) =
      right * residual left leftSums + left * residual right rightSums := by
  simp only [residual, euler_product]
  ring

/-- The support connection is a reference for every prefix of its exact
finite positive-power row, including all initial powers. -/
theorem support_fits (roots : Finset Field) (observed : Nat) :
    ∀ power ≤ observed, (residual (supportConnection roots) (truncatedPowerSums roots observed)).coeff power = 0 := by
  classical
  induction roots using Finset.induction_on with
  | empty => simp [supportConnection, truncatedPowerSums, residual, euler]
  | insert root roots fresh ih =>
    intro power within
    simp only [supportConnection, truncatedPowerSums, Finset.prod_insert fresh, Finset.sum_insert fresh]
    change (residual ((1 - C root * X) * supportConnection roots)
      (singleSums root observed + truncatedPowerSums roots observed)).coeff power = 0
    rw [residual_product, coeff_add, coeff_mul_prefix_zero (supportConnection roots) _ power
      (fun i bound => factor_fits root observed i (bound.trans within)),
      coeff_mul_prefix_zero (1 - C root * X) _ power (fun i bound => ih i (bound.trans within)), zero_add]

private theorem single_sums_coeff (root : Field) (observed power : Nat) (within : power ≤ observed) :
    (singleSums root observed).coeff power = if power = 0 then 0 else root ^ power := by
  have term (i : Nat) : ((C root * X) ^ i).coeff power = if power = i then root ^ i else 0 := by
    rw [mul_pow, ← map_pow, coeff_C_mul_X_pow]
  unfold singleSums
  rw [coeff_sub, finsetSum_coeff, Finset.sum_eq_single power]
  · rw [term, ite_eq_left rfl, coeff_one]
    by_cases zero : power = 0
    · simp [zero]
    · simp [zero]
  · intro i _ distinct
    rw [term, ite_eq_right (Ne.symm distinct)]
  · intro missing
    exact (missing (Finset.mem_range.mpr (by omega))).elim

theorem power_sums_coeff (roots : Finset Field) (observed power : Nat) (within : power ≤ observed) :
    (truncatedPowerSums roots observed).coeff power =
      if power = 0 then 0 else Reconciliation.powerSum roots power := by
  simp only [truncatedPowerSums, finsetSum_coeff, single_sums_coeff _ _ _ within, Reconciliation.powerSum]
  split <;> simp

private theorem residual_coeff_congr (row left right : Polynomial Field) (power : Nat)
    (same : ∀ i ≤ power, left.coeff i = right.coeff i) :
    (residual row left).coeff power = (residual row right).coeff power := by
  simp only [residual, coeff_add, coeff_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro ij member
  have equation := Finset.mem_antidiagonal.mp member
  rw [same ij.2 (by omega)]

/-- The native finite syndrome row fits the reference when its positive
words represent the distinct support's power sums. The sentinel is
excluded by `syndromePolynomial`. -/
theorem reference_fits_words (roots : Finset Field) (syndromes : Slice U64) (observed : Nat)
    (room : observed < syndromes.length)
    (moments : ∀ i, 0 < i → i ≤ observed → toField syndromes[i]!.bv = Reconciliation.powerSum roots i) :
    ∀ i ≤ observed, (residual (supportConnection roots) (syndromePolynomial syndromes)).coeff i = 0 := by
  intro power within
  rw [residual_coeff_congr _ _ (truncatedPowerSums roots observed) power]
  · exact support_fits roots observed power within
  · intro i bound
    rw [power_sums_coeff roots observed i (bound.trans within)]
    unfold syndromePolynomial
    rw [coeff_boundedPolynomial, ite_eq_left (by omega)]
    by_cases zero : i = 0
    · rw [ite_eq_left zero, ite_eq_left zero]
    · rw [ite_eq_right zero, ite_eq_right zero, moments i (by omega) (bound.trans within)]

/-- For an honest support, the source candidate cannot grow past the
support cardinality while its observed positive power sums remain available. -/
theorem native_candidate_bound (roots : Finset Field) (syndromes connection previous : Slice U64)
    (index degree previousLen shift observed : Nat) (scale delta : U64)
    (inv : BmResidualInvariant.Invariant syndromes connection previous index degree previousLen shift scale)
    (degreeBound : degree ≤ roots.card)
    (processed : index + 1 ≤ observed) (room : observed < syndromes.length)
    (moments : ∀ i, 0 < i → i ≤ observed → toField syndromes[i]!.bv = Reconciliation.powerSum roots i)
    (current : (residual (connectionPolynomial connection degree) (syndromePolynomial syndromes)).coeff
      (index + 1) = toField delta.bv) (nonzero : delta ≠ 0#u64) :
    BmScalar.candidateDegree index degree ≤ roots.card := by
  have nonzeroResidual : (residual (connectionPolynomial connection degree)
      (syndromePolynomial syndromes)).coeff (index + 1) ≠ 0 := by
    rw [current]
    intro zero
    apply nonzero
    apply U64.bv_eq_imp_eq
    apply toField_injective
    change toField delta.bv = toField 0
    rwa [toField_zero]
  have bound := discrepancy_degree_bound _ (supportConnection roots) _ (index + 1)
    (support_constant roots) (fun i hi => reference_fits_words roots syndromes observed room moments
      i (hi.trans processed)) inv.earlier nonzeroResidual
  have currentDegree := connection_degree connection degree
  have referenceDegree := support_degree roots
  unfold BmScalar.candidateDegree
  split <;> omega

/-- A residual zero prefix gives the positive-moment recurrence for the
reciprocal of the active connection. -/
theorem reverse_recurs (roots : Finset Field) (syndromes : Slice U64) (row : Polynomial Field)
    (observed : Nat) (room : observed < syndromes.length) (constant : row.coeff 0 ≠ 0)
    (moments : ∀ i, 0 < i → i ≤ observed → toField syndromes[i]!.bv = Reconciliation.powerSum roots i)
    (fits : ∀ i ≤ observed, (residual row (syndromePolynomial syndromes)).coeff i = 0) :
    Reconciliation.positiveRecurrenceThrough roots row.reverse observed := by
  have reverseDegree : row.reverse.natDegree = row.natDegree := by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr constant), Nat.sub_zero]
  intro start positive within
  rw [reverseDegree] at within
  let power := start + row.natDegree
  have window : power ≤ observed := within
  have beyond : row.natDegree < power := by omega
  have zero : (row * syndromePolynomial syndromes).coeff power = 0 := by
    rw [← BmParity.current_discrepancy row (syndromePolynomial syndromes) power beyond]
    exact fits power window
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at zero
  simp only [Reconciliation.positiveRecurrenceSum, reverseDegree]
  rw [← Finset.sum_range_reflect]
  calc
    _ = ∑ i ∈ Finset.range (row.natDegree + 1),
        row.coeff i * (syndromePolynomial syndromes).coeff (power - i) := by
      apply Finset.sum_congr rfl
      intro i member
      have bound := Finset.mem_range.mp member
      have reversed : row.natDegree + 1 - 1 - i = row.natDegree - i := by omega
      rw [reversed, coeff_reverse, revAt_le (by omega), show row.natDegree - (row.natDegree - i) = i by omega]
      have lag : start + (row.natDegree - i) = power - i := by omega
      rw [lag]
      unfold syndromePolynomial
      rw [coeff_boundedPolynomial, ite_eq_left (by omega), ite_eq_right (by omega), moments]
      all_goals omega
    _ = _ := by
      rw [← zero]
      apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
      intro i _ outside
      have large : ¬ i < row.natDegree + 1 := fun less => outside (Finset.mem_range.mpr less)
      rw [coeff_eq_zero_of_natDegree_lt (show row.natDegree < i by omega), zero_mul]

/-- Under a bounded honest support, the finished native degree is exact
and the leading coefficient cannot trigger InvalidLocator. -/
theorem exact_terminal_degree (roots : Finset Field) (syndromes connection previous : Slice U64)
    (index degree previousLen shift : Nat) (scale : U64)
    (inv : BmResidualInvariant.Invariant syndromes connection previous index degree previousLen shift scale)
    (noZero : (0 : Field) ∉ roots) (degreeBound : degree ≤ roots.card)
    (enough : 2 * roots.card ≤ index) (room : index < syndromes.length)
    (moments : ∀ i, 0 < i → i ≤ index → toField syndromes[i]!.bv = Reconciliation.powerSum roots i) :
    (connectionPolynomial connection degree).natDegree = degree ∧ degree = roots.card ∧
      connection[degree]! ≠ 0#u64 := by
  let row := connectionPolynomial connection degree
  have rowDegree : row.natDegree ≤ degree := connection_degree connection degree
  have constant : row.coeff 0 ≠ 0 := by
    intro zero
    change (connectionPolynomial connection degree).coeff 0 = 0 at zero
    unfold connectionPolynomial at zero
    rw [coeff_boundedPolynomial, ite_eq_left (by omega)] at zero
    apply inv.constant
    apply U64.bv_eq_imp_eq
    apply toField_injective
    change toField connection[(0 : Nat)]!.bv = toField 0
    rwa [toField_zero]
  have rowNonzero : row ≠ 0 := by
    intro rowZero
    apply constant
    rw [rowZero, coeff_zero]
  have reverseDegree : row.reverse.natDegree = row.natDegree := by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr constant), Nat.sub_zero]
  have fits : Reconciliation.positiveRecurrenceThrough roots row.reverse index :=
    reverse_recurs roots syndromes row index room constant moments (fun i hi => inv.earlier i (by omega))
  have lower := (Reconciliation.positive_locator_minimal roots row.reverse index noZero
    (fun h => rowNonzero (reverse_eq_zero.mp h)) (by omega) fits).2
  have exactDegree : row.natDegree = degree := by omega
  refine ⟨exactDegree, by omega, ?_⟩
  intro wordZero
  have lead : row.coeff degree ≠ 0 := exactDegree ▸ (leadingCoeff_ne_zero.mpr rowNonzero)
  apply lead
  unfold row connectionPolynomial
  rw [coeff_boundedPolynomial, ite_eq_left (by omega), wordZero]
  exact toField_zero

/-- The exact ascending words written by the original terminal branch
encode the monic product of the honest support factors. -/
theorem exact_normalized_locator (roots : Finset Field) (syndromes connection previous : Slice U64)
    (index degree previousLen shift : Nat) (scale : U64)
    (inv : BmResidualInvariant.Invariant syndromes connection previous index degree previousLen shift scale)
    (noZero : (0 : Field) ∉ roots) (degreeBound : degree ≤ roots.card)
    (enough : 2 * roots.card ≤ index) (room : index < syndromes.length)
    (connectionRoom : degree < connection.length)
    (moments : ∀ i, 0 < i → i ≤ index → toField syndromes[i]!.bv = Reconciliation.powerSum roots i) :
    connectionPolynomial (BmTerminal.normalizedConnection connection degree) degree =
      Reconciliation.supportLocator roots := by
  obtain ⟨rowDegree, exactDegree, _⟩ :=
    exact_terminal_degree roots syndromes connection previous index degree previousLen shift scale
      inv noZero degreeBound enough room moments
  let row := connectionPolynomial connection degree
  let normalized := BmTerminal.normalizedConnection connection degree
  let candidate := connectionPolynomial normalized degree
  have head : row.coeff 0 = toField connection[(0 : Nat)]!.bv := by
    change (connectionPolynomial connection degree).coeff 0 = _
    rw [connectionPolynomial, coeff_boundedPolynomial, ite_eq_left (by omega)]
  have constant : row.coeff 0 ≠ 0 := head ▸ AffineQuartic.nonzero_field _ inv.constant
  have reversedDegree : row.reverse.natDegree = degree := by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr constant), Nat.sub_zero]
    exact rowDegree
  have normalizedReverse : candidate = C ((row.coeff 0)⁻¹) * row.reverse := by
    ext i
    change (connectionPolynomial normalized degree).coeff i = _
    rw [connectionPolynomial, coeff_boundedPolynomial, coeff_C_mul]
    by_cases active : i < degree + 1
    · rw [ite_eq_left active, coeff_reverse, show row.natDegree = degree from rowDegree,
        revAt_le (by omega)]
      have coefficient : row.coeff (degree - i) = toField connection[degree - i]!.bv := by
        change (connectionPolynomial connection degree).coeff (degree - i) = _
        rw [connectionPolynomial, coeff_boundedPolynomial, ite_eq_left (by omega)]
      rw [coefficient, head, mul_comm]
      unfold normalized
      rw [BmReciprocalMeaning.normalized_word connection degree i connectionRoom (by omega)]
      change toField (multiplyWord connection[degree - i]!.bv
        (BmTerminal.inverseWord connection[(0 : Nat)]!).bv) = _
      rw [toField_mul]
      exact congrArg (toField connection[degree - i]!.bv * ·) (wordFieldEquiv.apply_symm_apply _)
    · rw [ite_eq_right active, coeff_eq_zero_of_natDegree_lt (p := row.reverse) (by omega), mul_zero]
  have leading : candidate.coeff degree = 1 := by
    change (connectionPolynomial normalized degree).coeff degree = _
    rw [connectionPolynomial, coeff_boundedPolynomial, ite_eq_left (by omega)]
    exact BmReciprocalMeaning.normalized_leading connection degree connectionRoom inv.constant
  have candidateDegree : candidate.natDegree = degree :=
    Nat.le_antisymm (connection_degree normalized degree) (le_natDegree_of_ne_zero (by rw [leading]; exact one_ne_zero))
  have monic : candidate.Monic := by
    rw [Monic, leadingCoeff, candidateDegree, leading]
  have recurs : Reconciliation.positiveRecurrenceThrough roots row.reverse index :=
    reverse_recurs roots syndromes row index room constant moments (fun i hi => inv.earlier i (by omega))
  apply Reconciliation.positive_locator_unique roots candidate index noZero monic (by omega) (by omega)
  intro start positive within
  have zero := recurs start positive (by omega)
  rw [Reconciliation.positiveRecurrenceSum, reversedDegree] at zero
  rw [Reconciliation.positiveRecurrenceSum, candidateDegree, normalizedReverse]
  simp_rw [coeff_C_mul, mul_assoc]
  rw [← Finset.mul_sum, zero, mul_zero]

end BulksketchBridge.BmSupportBounds
