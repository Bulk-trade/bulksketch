import BulksketchBridge.BmUpdatePolynomial
import BulksketchBridge.BmCurrentDiscrepancy
import BulksketchBridge.BmEntrySpec

namespace BulksketchBridge.BmResidualInvariant

open Aeneas.Std Algebra.Gf64 Polynomial DenseCoefficient RebuiltLfsr BmSyndromePolynomials

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

noncomputable def previousPolynomial (previous : Slice U64) (previousLen : Nat) : Polynomial Field :=
  boundedPolynomial (fun i => toField previous[i]!.bv) previousLen

/-- The retained row has its first nonzero residual at the last growth
power. Before any growth, the initial row instead contributes the
constant coefficient of its shifted Euler term. -/
def Anchor (syndromes previous : Polynomial Field) (index shift : Nat) (scale : U64) : Prop :=
  ∃ power, index + 1 = power + shift ∧
    ((power = 0 ∧ previous = 1 ∧ scale = 1#u64) ∨
      (power % 2 = 1 ∧ (∀ i < power, (BmParity.residual previous syndromes).coeff i = 0) ∧
        (BmParity.residual previous syndromes).coeff power = toField scale.bv))

/-- A native loop state carries the residual zero prefix, two nonzero
words and the anchor represented by its actual retained row and shift. -/
structure Invariant (syndromes connection previous : Slice U64)
    (index degree previousLen shift : Nat) (scale : U64) : Prop where
  earlier : ∀ i < index + 1,
    (BmParity.residual (connectionPolynomial connection degree) (syndromePolynomial syndromes)).coeff i = 0
  constant : connection[(0 : Nat)]! ≠ 0#u64
  scaleNonzero : scale ≠ 0#u64
  anchor : Anchor (syndromePolynomial syndromes) (previousPolynomial previous previousLen) index shift scale

private theorem constant_polynomial (row : Slice U64) (one : row[(0 : Nat)]! = 1#u64) :
    connectionPolynomial row 0 = 1 := by
  ext i
  unfold connectionPolynomial
  rw [coeff_boundedPolynomial, coeff_one]
  by_cases zero : i = 0
  · subst i
    rw [ite_eq_left (by decide), ite_eq_left rfl, one]
    exact toField_one
  · rw [ite_eq_right (by omega), ite_eq_right zero]

theorem initial (syndromes connection previous : Slice U64)
    (connectionOne : connection[(0 : Nat)]! = 1#u64) (previousOne : previous[(0 : Nat)]! = 1#u64) :
    Invariant syndromes connection previous 0 0 1 1 1#u64 := by
  have oneNonzero : (1#u64 : U64) ≠ 0#u64 := by decide
  refine ⟨?_, connectionOne ▸ oneNonzero, oneNonzero, ⟨0, rfl, Or.inl ⟨rfl, ?_, rfl⟩⟩⟩
  · intro i below
    have iz : i = 0 := by omega
    subst i
    rw [constant_polynomial connection connectionOne]
    simp [BmParity.residual, BmParity.euler, syndrome_coeff_zero]
  · exact constant_polynomial previous previousOne

/-- The original entry clears its admitted prefix and writes one in the
first coefficient of each live row. -/
theorem initial_buffer (words : Slice U64) (budget : Usize) (nonempty : 0 < words.length) :
    (BmEntry.initialBuffer words budget)[(0 : Nat)]! = 1#u64 := by
  unfold BmEntry.initialBuffer
  rw [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_eq]
  rw [restore_length]
  exact nonempty

theorem initialized (syndromes connection previous : Slice U64) (budget : Usize)
    (nonemptyConnection : 0 < connection.length) (nonemptyPrevious : 0 < previous.length) :
    Invariant syndromes (BmEntry.initialBuffer connection budget) (BmEntry.initialBuffer previous budget)
      0 0 1 1 1#u64 :=
  initial syndromes _ _ (initial_buffer connection budget nonemptyConnection)
    (initial_buffer previous budget nonemptyPrevious)

private theorem anchor_advance {syndromes previous : Polynomial Field} {index shift : Nat} {scale : U64}
    (anchor : Anchor syndromes previous index shift scale) :
    Anchor syndromes previous (index + 1) (shift + 1) scale := by
  obtain ⟨power, aligned, properties⟩ := anchor
  exact ⟨power, by omega, properties⟩

theorem advance {syndromes connection previous : Slice U64} {index degree previousLen shift : Nat} {scale : U64}
    (inv : Invariant syndromes connection previous index degree previousLen shift scale)
    (current : (BmParity.residual (connectionPolynomial connection degree)
      (syndromePolynomial syndromes)).coeff (index + 1) = 0) :
    Invariant syndromes connection previous (index + 1) degree previousLen (shift + 1) scale := by
  refine ⟨?_, inv.constant, inv.scaleNonzero, anchor_advance inv.anchor⟩
  intro i below
  by_cases last : i = index + 1
  · simpa only [last] using current
  · exact inv.earlier i (by omega)

theorem odd_advance {difference initial syndromes connection previous : Slice U64}
    {index degree previousLen shift processed : Nat} {scale : U64}
    (inv : Invariant syndromes connection previous index degree previousLen shift scale)
    (odd : index % 2 = 1) (degreeBound : degree ≤ index)
    (syndromeBound : index + 1 < syndromes.length) (processedBound : index + 1 < processed)
    (reconstructed : Reconstruction.Prefix difference initial syndromes processed) :
    Invariant syndromes connection previous (index + 1) degree previousLen (shift + 1) scale := by
  apply advance inv
  have degreeActual := connection_degree connection degree
  rw [BmParity.current_discrepancy _ _ _ (by omega),
    discrepancy_polynomial connection syndromes degree (index + 1) (by omega) syndromeBound]
  exact reconstructed_skip connection difference initial syndromes degree (index + 1) processed
    (by omega) (by omega) processedBound syndromeBound reconstructed inv.earlier

private theorem anchor_equations (syndromes previous : Polynomial Field) (index shift : Nat) (scale : U64)
    (anchor : Anchor syndromes previous index shift scale) (even : index % 2 = 0)
    (syndromeZero : syndromes.coeff 0 = 0) :
    ∃ power, index + 1 = power + shift ∧
      (∀ i < power, (BmParity.residual previous syndromes + C (shift : Field) * previous).coeff i = 0) ∧
      (BmParity.residual previous syndromes + C (shift : Field) * previous).coeff power =
        toField scale.bv := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  obtain ⟨power, aligned, bootstrap | regular⟩ := anchor
  · obtain ⟨rfl, rfl, rfl⟩ := bootstrap
    refine ⟨0, aligned, by omega, ?_⟩
    change (BmParity.residual 1 syndromes + C (shift : Field) * 1).coeff 0 = toField 1
    rw [toField_one]
    exact BmParity.bootstrap_anchor syndromes shift (by omega) syndromeZero
  · obtain ⟨oddPower, earlier, value⟩ := regular
    exact ⟨power, aligned, BmParity.regular_anchor previous syndromes shift power
      (toField scale.bv) (by omega) earlier value⟩

private theorem field_of_nonzero_word (word : U64) (nonzero : word ≠ 0#u64) : toField word.bv ≠ 0 := by
  intro zero
  apply nonzero
  apply U64.bv_eq_imp_eq
  apply toField_injective
  change toField word.bv = toField 0
  rw [toField_zero]
  exact zero

private theorem nonzero_word_of_field (word : U64) (nonzero : toField word.bv ≠ 0) : word ≠ 0#u64 := by
  intro zero
  apply nonzero
  subst word
  exact toField_zero

private theorem accepted_residual {syndromes connection previous : Slice U64}
    {index budget degree previousLen shift : Nat} {scale : U64}
    (inv : Invariant syndromes connection previous index degree previousLen shift scale)
    (scalar : BmScalar.Invariant index budget degree previousLen shift)
    (admitted : BmScalar.candidateDegree index degree ≤ budget)
    (connectionRoom : budget < connection.length) (previousRoom : budget < previous.length)
    (even : index % 2 = 0) (delta : U64)
    (current : (BmParity.residual (connectionPolynomial connection degree)
      (syndromePolynomial syndromes)).coeff (index + 1) = toField delta.bv) :
    let next := BmScalar.candidateDegree index degree
    let updated := BmConnectionUpdate.expectedConnection connection previous (degree + 1)
      next shift previousLen scale delta
    (∀ i < index + 1 + 1,
      (BmParity.residual (connectionPolynomial updated next) (syndromePolynomial syndromes)).coeff i = 0) ∧
      updated[(0 : Nat)]! ≠ 0#u64 := by
  obtain ⟨power, aligned, anchorEarlier, anchorValue⟩ :=
    anchor_equations _ _ index shift scale inv.anchor even (syndrome_coeff_zero syndromes)
  let next := BmScalar.candidateDegree index degree
  let updated := BmConnectionUpdate.expectedConnection connection previous (degree + 1)
    next shift previousLen scale delta
  change (∀ i < index + 1 + 1,
      (BmParity.residual (connectionPolynomial updated next) (syndromePolynomial syndromes)).coeff i = 0) ∧
    updated[(0 : Nat)]! ≠ 0#u64
  refine ⟨?_, ?_⟩
  · intro i bound
    exact BmUpdatePolynomial.accepted_preserves_residual connection previous syndromes degree index shift
      previousLen budget power scale delta scalar admitted connectionRoom previousRoom aligned inv.earlier
      current anchorEarlier anchorValue i (by omega)
  · obtain ⟨ordered, shifted, _⟩ :=
      BmScalar.shifted_window_bounds index budget degree previousLen shift scalar admitted
    have prevFit := Nat.le_trans scalar.previousBudget (by omega : budget + 1 ≤ previous.length)
    have nextFit : next < connection.length := Nat.lt_of_le_of_lt admitted connectionRoom
    have shiftPos := scalar.shiftPositive
    have head : updated[(0 : Nat)]! = BmMutable.mulWord scale connection[(0 : Nat)]! := by
      unfold updated
      rw [BmUpdatePolynomial.updated_word connection previous (degree + 1) next shift previousLen 0
        scale delta (by omega) nextFit shifted prevFit (Nat.zero_le _)]
      simp [show ¬ shift ≤ 0 by omega]
    rw [head]
    apply nonzero_word_of_field
    change toField (multiplyWord scale.bv connection[(0 : Nat)]!.bv) ≠ 0
    rw [toField_mul]
    exact mul_ne_zero (field_of_nonzero_word scale inv.scaleNonzero) (field_of_nonzero_word _ inv.constant)

private theorem copied_prefix_polynomial (connection previous : Slice U64) (degree : Nat)
    (connectionRoom : degree < connection.length) (previousRoom : degree < previous.length) :
    previousPolynomial (previous.setSlice! 0 (prefixSlice connection (degree + 1)).val) (degree + 1) =
      connectionPolynomial connection degree := by
  ext i
  simp only [previousPolynomial, connectionPolynomial, coeff_boundedPolynomial]
  have sourceRoom : degree < connection.val.length := connectionRoom
  have targetRoom : degree < previous.val.length := previousRoom
  by_cases active : i < degree + 1
  · simp only [active, ite_true, Slice.getElem!_Nat_eq, Slice.setSlice!_val]
    have patchLen := prefix_length connection (degree + 1)
    rw [Nat.min_eq_left (by omega)] at patchLen
    rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨Nat.zero_le _, by simpa only [Nat.sub_zero] using
      (show i < (prefixSlice connection (degree + 1)).length by omega), by omega⟩, Nat.sub_zero]
    congr 2
    simp only [prefixSlice, Slice.from_val]
    simpa only [List.slice, List.drop_zero, Nat.sub_zero, Nat.zero_add] using
      List.getElem!_slice 0 (degree + 1) i connection.val ⟨by omega, by omega⟩
  · simp only [active, ite_false]

/-- The accepted no-growth branch retains the prior row and anchor. -/
theorem accepted_stay {syndromes connection previous : Slice U64}
    {index budget degree previousLen shift : Nat} {scale : U64}
    (inv : Invariant syndromes connection previous index degree previousLen shift scale)
    (scalar : BmScalar.Invariant index budget degree previousLen shift)
    (connectionRoom : budget < connection.length) (previousRoom : budget < previous.length)
    (even : index % 2 = 0) (stays : ¬ 2 * degree ≤ index) (delta : U64)
    (current : (BmParity.residual (connectionPolynomial connection degree)
      (syndromePolynomial syndromes)).coeff (index + 1) = toField delta.bv) :
    Invariant syndromes (BmConnectionUpdate.expectedConnection connection previous (degree + 1)
      degree shift previousLen scale delta) previous (index + 1) degree previousLen (shift + 1) scale := by
  have candidate : BmScalar.candidateDegree index degree = degree := by
    simp [BmScalar.candidateDegree, stays]
  obtain ⟨earlier, constant⟩ := accepted_residual inv scalar (candidate.symm ▸ scalar.degreeBudget)
    connectionRoom previousRoom even delta current
  simp only [candidate] at earlier constant
  exact ⟨earlier, constant, inv.scaleNonzero, anchor_advance inv.anchor⟩

/-- The accepted growth branch copies the pre-update connection into
the prior row, creating a new odd anchor at the current power. -/
theorem accepted_grow {syndromes connection previous : Slice U64}
    {index budget degree previousLen shift : Nat} {scale : U64}
    (inv : Invariant syndromes connection previous index degree previousLen shift scale)
    (scalar : BmScalar.Invariant index budget degree previousLen shift)
    (connectionRoom : budget < connection.length) (previousRoom : budget < previous.length)
    (even : index % 2 = 0) (grows : 2 * degree ≤ index) (delta : U64) (nonzero : delta ≠ 0#u64)
    (admitted : index + 1 - degree ≤ budget)
    (current : (BmParity.residual (connectionPolynomial connection degree)
      (syndromePolynomial syndromes)).coeff (index + 1) = toField delta.bv) :
    Invariant syndromes (BmConnectionUpdate.expectedConnection connection previous (degree + 1)
      (index + 1 - degree) shift previousLen scale delta)
      (previous.setSlice! 0 (prefixSlice connection (degree + 1)).val)
      (index + 1) (index + 1 - degree) (degree + 1) 1 delta := by
  have candidate : BmScalar.candidateDegree index degree = index + 1 - degree := by
    simp [BmScalar.candidateDegree, grows]
  obtain ⟨earlier, constant⟩ := accepted_residual inv scalar (candidate.symm ▸ admitted)
    connectionRoom previousRoom even delta current
  simp only [candidate] at earlier constant
  refine ⟨earlier, constant, nonzero, ⟨index + 1, rfl, Or.inr ⟨by omega, ?_⟩⟩⟩
  have oldBound := scalar.degreeBudget
  rw [copied_prefix_polynomial connection previous degree (by omega) (by omega)]
  exact ⟨inv.earlier, current⟩

/-- Any positive recurrence start whose whole window was processed has
zero native discrepancy. This is the finite positive-moment relation
used to identify the reciprocal locator. -/
theorem recurrence_sum {syndromes connection previous : Slice U64}
    {index degree previousLen shift : Nat} {scale : U64}
    (inv : Invariant syndromes connection previous index degree previousLen shift scale)
    (power : Nat) (degreeBound : degree < power) (processed : power ≤ index)
    (syndromeBound : power < syndromes.length) :
    ∑ i ∈ Finset.range (degree + 1), toField connection[i]!.bv * toField syndromes[power - i]!.bv = 0 := by
  have degreeActual := connection_degree connection degree
  rw [← discrepancy_polynomial connection syndromes degree power degreeBound syndromeBound,
    ← BmParity.current_discrepancy _ _ _ (by omega)]
  exact inv.earlier power (by omega)

end BulksketchBridge.BmResidualInvariant
