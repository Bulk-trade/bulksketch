import BulksketchBridge.BmConnectionUpdate
import BulksketchBridge.BmSyndromePolynomials
import BulksketchBridge.Algebra.WordOps
import BulksketchBridge.BmScalar

namespace BulksketchBridge.BmUpdatePolynomial

open Aeneas.Std BmMutable BmConnectionUpdate BmSyndromePolynomials
open DenseCoefficient RebuiltLfsr Algebra.Gf64 Polynomial

set_option maxRecDepth 4096

private theorem set_inside (words patch : Slice U64) (start i : Nat)
    (low : start ≤ i) (high : i - start < patch.length) (room : i < words.length) :
    (words.setSlice! start patch.val)[i]! = patch[i - start]! := by
  simp only [Slice.getElem!_Nat_eq, Slice.setSlice!_val]
  exact List.getElem!_setSlice!_middle _ _ _ _ ⟨low, high, room⟩

private theorem set_outside (words patch : Slice U64) (start i : Nat)
    (outside : i < start ∨ start + patch.length ≤ i) :
    (words.setSlice! start patch.val)[i]! = words[i]! := by
  simp only [Slice.getElem!_Nat_eq, Slice.setSlice!_val]
  exact List.getElem!_setSlice!_same _ _ _ _ outside

private theorem prefix_word (words : Slice U64) (count i : Nat)
    (bound : count ≤ words.length) (active : i < count) :
    (prefixSlice words count)[i]! = words[i]! := by
  simp only [Slice.getElem!_Nat_eq, prefixSlice, Slice.from_val]
  simpa only [List.slice, List.drop_zero, Nat.sub_zero, Nat.zero_add] using
    List.getElem!_slice 0 count i words.val ⟨bound, by omega⟩

private theorem region_word (words : Slice U64) (start stop i : Nat)
    (bound : stop ≤ words.length) (active : start + i < stop) :
    (ClosedLeaf.region words start stop)[i]! = words[start + i]! := by
  simp only [Slice.getElem!_Nat_eq, ClosedLeaf.region, Slice.from_val]
  exact List.getElem!_slice _ _ _ _ ⟨bound, active⟩

private theorem prepared_word (connection : Slice U64) (len nextDegree i : Nat) (scale : U64)
    (ordered : len ≤ nextDegree + 1) (fit : nextDegree < connection.length)
    (active : i ≤ nextDegree) :
    (clearedConnection (scaledConnection connection len scale) len nextDegree)[i]! =
      if i < len then mulWord scale connection[i]! else 0#u64 := by
  let head := prefixSlice connection len
  let scaled := scaledConnection connection len scale
  let gap := ClosedLeaf.region scaled len (nextDegree + 1)
  have headLen : head.length = len := (prefix_length _ _).trans (Nat.min_eq_left (by omega))
  have scaledLen : scaled.length = connection.length := Slice.setSlice!_length _ _ _
  have gapLen : gap.length = nextDegree + 1 - len :=
    ClosedLeaf.region_length _ _ _ (by omega)
  have zeroLen : (zeroWords gap).length = gap.length := by simp [zeroWords, Slice.length]
  change (scaled.setSlice! len (zeroWords gap).val)[i]! = _
  by_cases old : i < len
  · rw [ite_eq_left old, set_outside _ _ _ _ (Or.inl old)]
    change (connection.setSlice! 0 (patchWords (fun j => mulWord scale head[j]!)
      0 head.length head).val)[i]! = _
    rw [set_inside _ _ _ _ (by omega) (by rw [patchWords_length, headLen]; omega) (by omega)]
    rw [Nat.sub_zero, patchWords_word _ _ _ _ _ (by omega), ite_eq_left (by omega),
      prefix_word connection len i (by omega) old]
  · rw [ite_eq_right old, set_inside _ _ _ _ (by omega) (by omega) (by omega)]
    simp only [zeroWords, Slice.getElem!_Nat_eq, Slice.from_val]
    rw [List.getElem!_replicate]
    omega

theorem updated_word (connection previous : Slice U64) (len nextDegree shift previousLen i : Nat)
    (scale delta : U64) (ordered : len ≤ nextDegree + 1) (fit : nextDegree < connection.length)
    (shifted : shift + previousLen ≤ nextDegree + 1) (prevFit : previousLen ≤ previous.length)
    (active : i ≤ nextDegree) :
    let base := if i < len then mulWord scale connection[i]! else 0#u64
    (expectedConnection connection previous len nextDegree shift previousLen scale delta)[i]! =
      if shift ≤ i ∧ i < shift + previousLen then
        shiftedWord delta base previous[i - shift]! else base := by
  dsimp only
  let cleared := clearedConnection (scaledConnection connection len scale) len nextDegree
  let left := ClosedLeaf.region cleared shift (shift + previousLen)
  let right := prefixSlice previous previousLen
  have clearedLen : cleared.length = connection.length := by
    unfold cleared clearedConnection scaledConnection
    simp only [Slice.setSlice!_length]
  have leftLen : left.length = previousLen := by
    rw [ClosedLeaf.region_length _ _ _ (by omega), Nat.add_sub_cancel_left]
  have rightLen : right.length = previousLen := (prefix_length _ _).trans (Nat.min_eq_left prevFit)
  let patch := patchWords (fun j => shiftedWord delta left[j]! right[j]!) 0
    (min left.length right.length) left
  have patchLen : patch.length = previousLen := (patchWords_length _ _ _ _).trans leftLen
  have prepared := prepared_word connection len nextDegree i scale ordered fit active
  change (cleared.setSlice! shift patch.val)[i]! = _
  by_cases window : shift ≤ i ∧ i < shift + previousLen
  · rw [ite_eq_left window, set_inside _ _ _ _ window.1 (by omega) (by omega)]
    unfold patch
    rw [patchWords_word _ _ _ _ _ (by omega), leftLen, rightLen, Nat.min_self, ite_eq_left (by omega),
      region_word cleared shift (shift + previousLen) _ (by omega) (by omega),
      prefix_word previous previousLen _ prevFit (by omega),
      Nat.add_sub_of_le window.1, prepared]
  · rw [ite_eq_right window, set_outside _ _ _ _ (by omega), prepared]

/-- The exact accepted connection slice denotes the homogeneous polynomial
update. Neither the uninitialized inactive words nor any writeback tail
enters the two active polynomial prefixes. -/
theorem update_polynomial (connection previous : Slice U64)
    (degree nextDegree shift previousLen : Nat) (scale delta : U64)
    (ordered : degree ≤ nextDegree) (fit : nextDegree < connection.length)
    (shifted : shift + previousLen ≤ nextDegree + 1) (prevFit : previousLen ≤ previous.length) :
    connectionPolynomial
      (expectedConnection connection previous (degree + 1) nextDegree shift previousLen scale delta)
      nextDegree =
      C (toField scale.bv) * connectionPolynomial connection degree +
        C (toField delta.bv) * (X ^ shift *
          boundedPolynomial (fun i => toField previous[i]!.bv) previousLen) := by
  have mapMul (a b : U64) : toField (mulWord a b).bv = toField a.bv * toField b.bv :=
    toField_mul a.bv b.bv
  have mapUpdate (b c : U64) :
      toField (shiftedWord delta b c).bv =
        toField b.bv + toField delta.bv * toField c.bv := by
    change toField (b.bv ^^^ (mulWord delta c).bv) = _
    rw [toField_xor, mapMul]
  ext i
  simp only [connectionPolynomial, coeff_boundedPolynomial, coeff_add, coeff_C_mul, coeff_X_pow_mul']
  by_cases inNext : i < nextDegree + 1
  · rw [ite_eq_left inNext, updated_word connection previous (degree + 1) nextDegree
      shift previousLen i scale delta (by omega) fit shifted prevFit (by omega)]
    let base := if i < degree + 1 then mulWord scale connection[i]! else 0#u64
    have baseField : toField base.bv =
        toField scale.bv * (if i < degree + 1 then toField connection[i]!.bv else 0) := by
      unfold base
      by_cases old : i < degree + 1
      · simp only [old, ite_true, mapMul]
      · simp only [old, ite_false, mul_zero]
        exact toField_zero
    change toField (if shift ≤ i ∧ i < shift + previousLen then
      shiftedWord delta base previous[i - shift]! else base).bv = _
    by_cases low : shift ≤ i
    · by_cases high : i < shift + previousLen
      · have prev : i - shift < previousLen := by omega
        simp only [low, high, and_self, ite_true, prev, mapUpdate, baseField]
      · have prev : ¬ i - shift < previousLen := by omega
        simp only [low, high, true_and, ite_true, ite_false, prev, mul_zero, add_zero, baseField]
    · simp only [low, false_and, ite_false, mul_zero, add_zero, baseField]
  · have outside : ¬ i < degree + 1 := by omega
    simp only [inNext, outside, ite_false, mul_zero, zero_add]
    by_cases low : shift ≤ i
    · have prev : ¬ i - shift < previousLen := by omega
      simp only [low, ite_true, prev, ite_false, mul_zero]
    · simp only [low, ite_false, mul_zero]

/-- Scalar admission supplies the full active update window. The native
slice update preserves the polynomial residual prefix once the actual
discrepancy and stored previous row satisfy the anchor equations. -/
theorem accepted_preserves_residual (connection previous syndromes : Slice U64)
    (degree index shift previousLen budget anchor : Nat) (scale delta : U64)
    (scalar : BmScalar.Invariant index budget degree previousLen shift)
    (admitted : BmScalar.candidateDegree index degree ≤ budget)
    (connectionRoom : budget < connection.length) (previousRoom : budget < previous.length)
    (aligned : index + 1 = anchor + shift)
    (earlier : ∀ i < index + 1,
      (BmParity.residual (connectionPolynomial connection degree) (syndromePolynomial syndromes)).coeff i = 0)
    (current : (BmParity.residual (connectionPolynomial connection degree)
      (syndromePolynomial syndromes)).coeff (index + 1) = toField delta.bv)
    (anchorEarlier : ∀ i < anchor,
      (BmParity.residual (boundedPolynomial (fun j => toField previous[j]!.bv) previousLen)
        (syndromePolynomial syndromes) +
        C (shift : Field) * boundedPolynomial (fun j => toField previous[j]!.bv) previousLen).coeff i = 0)
    (anchorValue :
      (BmParity.residual (boundedPolynomial (fun j => toField previous[j]!.bv) previousLen)
        (syndromePolynomial syndromes) +
        C (shift : Field) * boundedPolynomial (fun j => toField previous[j]!.bv) previousLen).coeff anchor =
        toField scale.bv) :
    ∀ i ≤ index + 1,
      (BmParity.residual
        (connectionPolynomial
          (expectedConnection connection previous (degree + 1) (BmScalar.candidateDegree index degree)
            shift previousLen scale delta) (BmScalar.candidateDegree index degree))
        (syndromePolynomial syndromes)).coeff i = 0 := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  obtain ⟨ordered, shifted, _⟩ := BmScalar.shifted_window_bounds index budget degree previousLen shift scalar admitted
  have fit := Nat.lt_of_le_of_lt admitted connectionRoom
  have prevFit := Nat.le_trans scalar.previousBudget (by omega : budget + 1 ≤ previous.length)
  rw [update_polynomial connection previous degree _ shift previousLen scale delta ordered fit shifted prevFit]
  exact BmParity.update_residual_prefix _ _ _ (index + 1) shift anchor
    (toField scale.bv) (toField delta.bv) aligned earlier current anchorEarlier anchorValue

end BulksketchBridge.BmUpdatePolynomial
