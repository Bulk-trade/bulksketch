import BulksketchBridge.RootSetup
import BulksketchBridge.RawMulTable

namespace BulksketchBridge.AffineMultiple

open Aeneas Aeneas.Std DenseCoefficient

/-- Exact shape bounds for the two factor matrices and the three work windows. -/
structure Layout (degree factorsLength workLength affineLength : Nat) : Prop where
  degree_min : 2 ≤ degree
  factor_room : degree * degree + degree * (degree + 1) ≤ factorsLength
  work_room : 2 * degree + (degree + 1) ≤ workLength
  affine_room : degree + 1 ≤ affineLength

/-- The source row workspace sizing admits the affine buffers whenever the
factor degree fits within the row budget. The BM prefix is the affine output. -/
theorem layout_from_row_budget {degree budget capacity factorsLength bmLength rawLength : Nat}
    (degreeMin : 2 ≤ degree) (degreeBudget : degree ≤ budget) (budgetCapacity : budget ≤ capacity)
    (factorsRoom : 2 * ((budget + 1) * (budget + 1)) ≤ factorsLength)
    (bmRoom : 4 * (capacity + 1) ≤ bmLength) (rawRoom : 2 * (budget + 2) ≤ rawLength) :
    Layout degree factorsLength (bmLength - (degree + 1)) (degree + 1) ∧
      2 * degree < rawLength := by
  have degreeSquare : degree * degree ≤ (budget + 1) * (budget + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have witnessMatrix : degree * (degree + 1) ≤ (budget + 1) * (budget + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  exact ⟨⟨degreeMin, by omega, by omega, Nat.le_refl _⟩, by omega⟩

theorem factor_layout {d factorsLength workLength affineLength : Nat}
    (h : Layout d factorsLength workLength affineLength) :
    d * d ≤ factorsLength ∧ d * (d + 1) ≤ factorsLength - d * d := by
  have room := h.factor_room
  omega

theorem work_layout {d factorsLength workLength affineLength : Nat}
    (h : Layout d factorsLength workLength affineLength) :
    d ≤ workLength ∧ d ≤ workLength - d ∧ d + 1 ≤ workLength - d - d := by
  have room := h.work_room
  omega

/-- Exact source endpoints for the trailing coefficient region of a pivot row. -/
theorem row_window {d row : Nat} (active : row < d) :
    row * d + row < (row + 1) * d ∧
    (row + 1) * d ≤ d * d ∧
    (row + 1) * d - (row * d + row) = d - row := by
  have expand : (row + 1) * d = row * d + d := by rw [Nat.add_mul, Nat.one_mul]
  have fits : (row + 1) * d ≤ d * d := Nat.mul_le_mul_right _ (by omega)
  omega

/-- Exact source endpoints for the populated witness prefix of a pivot row. -/
theorem witness_window {d row column : Nat} (active : row < d) (admitted : column ≤ d) :
    row * (d + 1) + (column + 1) ≤ d * (d + 1) ∧
    row * (d + 1) + (column + 1) - row * (d + 1) = column + 1 := by
  have expand : (row + 1) * (d + 1) = row * (d + 1) + (d + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
  have fits : (row + 1) * (d + 1) ≤ d * (d + 1) := Nat.mul_le_mul_right _ (by omega)
  omega

/-- The original checked subtraction and increment recover the polynomial's
width exactly for a nonempty slice. -/
theorem degree_width_normal (polynomial : Slice U64) (nonempty : 0 < polynomial.length) :
    ∃ degree : Usize,
      (Slice.len polynomial - 1#usize : Result Usize) = .ok degree ∧
      (degree + 1#usize : Result Usize) = .ok (Slice.len polynomial) ∧
      degree.val = polynomial.length - 1 := by
  obtain ⟨degree, subtractNormal, degreeValue, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := Slice.len polynomial) (y := 1#usize) (by
      rw [Slice.len_val]; change 1 ≤ polynomial.length; omega))
  change degree.val = (Slice.len polynomial).val - 1 at degreeValue
  rw [Slice.len_val] at degreeValue
  have maximum : polynomial.length ≤ Usize.max := polynomial.length_ineq
  obtain ⟨width, addNormal, widthValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := degree) (y := 1#usize) (by
      change degree.val + 1 ≤ Usize.max
      omega))
  change width.val = degree.val + 1 at widthValue
  have same : width = Slice.len polynomial := UScalar.eq_of_val_eq (by
    rw [widthValue, Slice.len_val]
    omega)
  exact ⟨degree, subtractNormal, same ▸ addNormal, degreeValue⟩

/-- An admitted affine matrix allocation bounds both checked Rust products. -/
theorem allocation_products (degree width : Usize) (factors : Slice U64)
    (widthValue : width.val = degree.val + 1)
    (room : degree.val * degree.val + degree.val * (degree.val + 1) ≤ factors.length) :
    ∃ rows witnesses : Usize,
      (degree * degree : Result Usize) = .ok rows ∧
      (degree * width : Result Usize) = .ok witnesses ∧
      rows.val = degree.val * degree.val ∧ witnesses.val = degree.val * (degree.val + 1) := by
  have maximum : factors.length ≤ Usize.max := factors.length_ineq
  obtain ⟨rows, rowsNormal, rowsValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.mul_spec (x := degree) (y := degree) (by omega))
  obtain ⟨witnesses, witnessNormal, witnessValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.mul_spec (x := degree) (y := width) (by rw [widthValue]; omega))
  exact ⟨rows, witnesses, rowsNormal, witnessNormal, rowsValue, by rwa [widthValue] at witnessValue⟩

/-- Every source row boundary, diagonal, and witness end is representable at
the machine width whenever the admitted matrix fits in its arena. -/
theorem checked_row_bounds (degree row column : Usize) (factors : Slice U64)
    (active : row.val < degree.val) (admitted : column.val ≤ degree.val)
    (room : degree.val * degree.val + degree.val * (degree.val + 1) ≤ factors.length) :
    row.val + 1 ≤ Usize.max ∧ column.val + 1 ≤ Usize.max ∧
    row.val * degree.val + row.val ≤ Usize.max ∧
    (row.val + 1) * degree.val ≤ Usize.max ∧
    row.val * (degree.val + 1) + column.val + 1 ≤ Usize.max := by
  have maximum : factors.length ≤ Usize.max := factors.length_ineq
  have ⟨diagonal, ending, _⟩ := row_window active
  have ⟨witnessEnd, _⟩ := witness_window active admitted
  have positive : 1 ≤ degree.val := by omega
  have widthFits : degree.val + 1 ≤ degree.val * (degree.val + 1) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (degree.val + 1) positive
  omega

/-- If each occupied pivot slot is new, one of the d+1 columns is dependent.
This is the finite-counting fact needed to rule out the final unreachable. -/
theorem some_dependent_column {d : Nat} (pivots : Fin (d + 1) → Option (Fin d))
    (neverReuse : ∀ (left right : Fin (d + 1)) (slot : Fin d),
      pivots left = some slot → pivots right = some slot → left = right) :
    ∃ column, pivots column = none := by
  by_contra noDependency
  have existsPivot (column : Fin (d + 1)) : ∃ pivot, pivots column = some pivot := by
    cases value : pivots column with
    | some pivot => exact ⟨pivot, rfl⟩
    | none => exact False.elim (noDependency ⟨column, value⟩)
  choose pivot equation using existsPivot
  have oneToOne : Function.Injective pivot := by
    intro left right equal
    apply neverReuse left right (pivot right) ((equation left).trans (congrArg some equal))
    exact equation right
  have impossible := Fintype.card_le_of_injective pivot oneToOne
  simp only [Fintype.card_fin] at impossible
  omega

end BulksketchBridge.AffineMultiple
