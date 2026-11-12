import Arithmetic.RootWorkBudgetGenerated
import BulksketchBridge.RootWorkBudgetMath
import BulksketchBridge.BmPrice
import BulksketchBridge.RawMulTable

namespace BulksketchBridge.RootWorkBudget

open Aeneas Aeneas.Std WorkSchedule
open bulksketch.decode.work
open core.result.Result.Insts (CoreOpsTry.branch)

set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

private theorem checked_value (units : Nat) (fits : units ≤ U64.max) :
    ∃ word : U64, checkedCost units = .Ok word ∧ word.val = units := by
  unfold checkedCost
  rw [dite_eq_left fits]
  exact ⟨_, rfl, UScalar.ofNatCore_val_eq _⟩

private theorem add_normal (a b : U64) (fits : a.val + b.val ≤ U64.max) :
    ∃ word : U64, add a b = .ok (.Ok word) ∧ word.val = a.val + b.val := by
  obtain ⟨word, normal, value⟩ := checked_value _ fits
  exact ⟨word, (BmPrice.add_refines a b).trans (congrArg Result.ok normal), value⟩

private theorem mul_normal (a b : U64) (fits : a.val * b.val ≤ U64.max) :
    ∃ word : U64, mul a b = .ok (.Ok word) ∧ word.val = a.val * b.val := by
  obtain ⟨word, normal, value⟩ := checked_value _ fits
  exact ⟨word, (mul_refines a b).trans (congrArg Result.ok normal), value⟩

private theorem div_normal (a b : U64) (nonzero : b.val ≠ 0) :
    ∃ word : U64, (a / b : Result U64) = .ok word ∧ word.val = a.val / b.val :=
  RawMulTable.normal_of_spec _ _ (U64.div_spec a nonzero)

private theorem sub_normal (a b : U64) (fits : b.val ≤ a.val) :
    ∃ word : U64, U64.checked_sub a b = some word ∧ word.val = a.val - b.val := by
  have spec := U64.checked_sub_bv_spec a b
  cases source : U64.checked_sub a b with
  | none =>
    rw [source] at spec
    omega
  | some word =>
    rw [source] at spec
    exact ⟨word, rfl, spec.2.1⟩

/-- Exact source arithmetic of the original native root bound throughout
    the full admitted u16 budget range. -/
def ActualNativeRootsBound : Prop :=
  ∀ budget : Usize, budget.val ≤ 65535 →
    ∃ units : U64, WorkScheduleV1.roots_bound budget = .ok (.Ok units) ∧
      units.val = rootsEnvelope budget.val

theorem native_roots_bound : ActualNativeRootsBound := by
  intro budget admitted
  let d := budget.val
  change d ≤ 65535 at admitted
  obtain ⟨r, converted, rValue⟩ := number_refines budget
  change r.val = d at rValue
  obtain ⟨leaves, leafCall, leafValue⟩ := mul_normal 160#u64 r (by
    change 160 * r.val ≤ U64.max
    rw [rValue, U64.max_eq]
    omega)
  change leaves.val = 160 * r.val at leafValue
  rw [rValue] at leafValue
  have leafEnvelope : leaves.val = 160 * d := leafValue
  by_cases small : d < 3
  · have compare : budget < 3#usize := by
      rw [UScalar.lt_equiv]
      exact small
    refine ⟨leaves, ?_, ?_⟩
    · simp only [WorkScheduleV1.roots_bound, converted, bind_ok, CoreOpsTry.branch, leafCall, compare, ite_true]
    · rw [roots_envelope_closed, closedRoots, ite_eq_left small, Nat.add_zero]
      exact leafEnvelope
  · have compare : ¬ budget < 3#usize := by
      rw [UScalar.lt_equiv]
      exact small
    have productHigh : d * (d + 1) ≤ 65535 * 65536 := Nat.mul_le_mul admitted (by omega)
    have squareHigh : d * (d + 1) * (2 * d + 1) ≤ 65535 * 65536 * 131071 :=
      Nat.mul_le_mul productHigh (by omega)
    have productLow : 3 * 4 ≤ d * (d + 1) := Nat.mul_le_mul (by omega) (by omega)
    have squareLow : 3 * 4 * 7 ≤ d * (d + 1) * (2 * d + 1) :=
      Nat.mul_le_mul productLow (by omega)
    obtain ⟨next, nextCall, nextValue⟩ := add_normal r 1#u64 (by
      change r.val + 1 ≤ U64.max
      rw [rValue, U64.max_eq]
      omega)
    change next.val = r.val + 1 at nextValue
    rw [rValue] at nextValue
    obtain ⟨product, productCall, productValue⟩ := mul_normal r next (by
      rw [rValue, nextValue, U64.max_eq]
      omega)
    rw [rValue, nextValue] at productValue
    obtain ⟨double, doubleCall, doubleValue⟩ := mul_normal 2#u64 r (by
      change 2 * r.val ≤ U64.max
      rw [rValue, U64.max_eq]
      omega)
    change double.val = 2 * r.val at doubleValue
    rw [rValue] at doubleValue
    obtain ⟨odd, oddCall, oddValue⟩ := add_normal double 1#u64 (by
      change double.val + 1 ≤ U64.max
      rw [doubleValue, U64.max_eq]
      omega)
    change odd.val = double.val + 1 at oddValue
    rw [doubleValue] at oddValue
    obtain ⟨numerator, numeratorCall, numeratorValue⟩ := mul_normal product odd (by
      rw [productValue, oddValue, U64.max_eq]
      omega)
    rw [productValue, oddValue] at numeratorValue
    obtain ⟨squares, squareCall, squareValue⟩ := div_normal numerator 6#u64 (by decide)
    obtain ⟨linear, linearCall, linearValue⟩ := div_normal product 2#u64 (by decide)
    change squares.val = numerator.val / 6 at squareValue
    change linear.val = product.val / 2 at linearValue
    rw [numeratorValue] at squareValue
    rw [productValue] at linearValue
    obtain ⟨squareTail, squareSub, squareTailValue⟩ := sub_normal squares 5#u64 (by
      change 5 ≤ squares.val
      rw [squareValue]
      omega)
    obtain ⟨linearTail, linearSub, linearTailValue⟩ := sub_normal linear 3#u64 (by
      change 3 ≤ linear.val
      rw [linearValue]
      omega)
    obtain ⟨nodes, nodeSub, nodesValue⟩ := sub_normal r 2#u64 (by
      change 2 ≤ r.val
      rw [rValue]
      omega)
    change squareTail.val = squares.val - 5 at squareTailValue
    change linearTail.val = linear.val - 3 at linearTailValue
    change nodes.val = r.val - 2 at nodesValue
    rw [squareValue] at squareTailValue
    rw [linearValue] at linearTailValue
    rw [rValue] at nodesValue
    have squareTailHigh : squareTail.val ≤ 65535 * 65536 * 131071 := by
      rw [squareTailValue]
      omega
    have linearTailHigh : linearTail.val ≤ 65535 * 65536 := by
      rw [linearTailValue]
      omega
    have nodesHigh : nodes.val ≤ 65535 := by rw [nodesValue]; omega
    obtain ⟨squareCost, squareCostCall, squareCostValue⟩ := mul_normal 12812#u64 squareTail (by
      change 12812 * squareTail.val ≤ U64.max
      rw [U64.max_eq]
      omega)
    obtain ⟨linearCost, linearCostCall, linearCostValue⟩ := mul_normal 17486#u64 linearTail (by
      change 17486 * linearTail.val ≤ U64.max
      rw [U64.max_eq]
      omega)
    obtain ⟨fixedCost, fixedCostCall, fixedCostValue⟩ := mul_normal 16968#u64 nodes (by
      change 16968 * nodes.val ≤ U64.max
      rw [U64.max_eq]
      omega)
    change squareCost.val = 12812 * squareTail.val at squareCostValue
    change linearCost.val = 17486 * linearTail.val at linearCostValue
    change fixedCost.val = 16968 * nodes.val at fixedCostValue
    obtain ⟨variableCost, variableCostCall, variableCostValue⟩ := add_normal squareCost linearCost (by
      rw [U64.max_eq]
      omega)
    obtain ⟨internalCost, internalCostCall, internalCostValue⟩ := add_normal variableCost fixedCost (by
      rw [U64.max_eq]
      omega)
    obtain ⟨total, totalCall, totalValue⟩ := add_normal leaves internalCost (by
      rw [U64.max_eq]
      omega)
    refine ⟨total, ?_, ?_⟩
    · simp only [WorkScheduleV1.roots_bound, converted, bind_ok, CoreOpsTry.branch, leafCall,
        compare, ite_false, nextCall, productCall, doubleCall, oddCall, numeratorCall,
        squareCall, linearCall, lift, squareSub, linearSub, nodeSub, core.option.Option.ok_or,
        squareCostCall, linearCostCall, variableCostCall, fixedCostCall, internalCostCall, totalCall]
    · rw [roots_envelope_closed, closedRoots, ite_eq_right small, totalValue, leafEnvelope,
        internalCostValue, variableCostValue, squareCostValue, linearCostValue, fixedCostValue,
        squareTailValue, linearTailValue, nodesValue]

def ActualNativeProperFactorTreeBudget : Prop :=
  ∀ (budget : Usize) (degree charged : Nat), budget.val ≤ 65535 → degree ≤ budget.val →
    ChargedFactorTree degree charged →
    ∃ units : U64, WorkScheduleV1.roots_bound budget = .ok (.Ok units) ∧ charged ≤ units.val

theorem native_proper_factor_tree_budget : ActualNativeProperFactorTreeBudget := by
  intro budget degree charged admitted fit tree
  obtain ⟨units, priced, value⟩ := native_roots_bound budget admitted
  exact ⟨units, priced, value ▸ proper_binary_tree_bound tree fit⟩

/-- Exact native prices for the six operations in the non-affine
    node envelope. Each Rust work charge succeeds at every admitted degree. -/
def ActualNativeRootNodePrices : Prop :=
  ∀ (degree : Usize), degree.val ≤ 65535 →
    (∃ units : U64, WorkScheduleV1.cost (.Table degree) = .ok (.Ok units) ∧ units.val = tableUnits degree.val) ∧
    (∃ units : U64, WorkScheduleV1.cost (.Trace degree) = .ok (.Ok units) ∧ units.val = traceUnits degree.val) ∧
    (∃ units : U64, WorkScheduleV1.cost (.SplitCheck degree) = .ok (.Ok units) ∧ units.val = splitCheckUnits degree.val) ∧
    (∃ units : U64, WorkScheduleV1.cost (.Gcd degree) = .ok (.Ok units) ∧ units.val = gcdUnits degree.val) ∧
    (∃ units : U64, WorkScheduleV1.cost (.Divide degree) = .ok (.Ok units) ∧ units.val = divideUnits degree.val) ∧
    (∃ units : U64, WorkScheduleV1.cost (.SplitAssembly degree) = .ok (.Ok units) ∧ units.val = assemblyUnits degree.val)

theorem native_root_node_prices : ActualNativeRootNodePrices := by
  intro degree bounded
  let d := degree.val
  change d ≤ 65535 at bounded
  have squareBound : d * d ≤ 65535 * 65535 := Nat.mul_le_mul bounded bounded
  have widthBound : (d + 1) * (d + 1) ≤ 65536 * 65536 :=
    Nat.mul_le_mul (by omega) (by omega)
  obtain ⟨word, numberCall, wordValue⟩ := number_refines degree
  change word.val = d at wordValue
  obtain ⟨squareWord, squareCall, squareValue⟩ := mul_normal word word (by rw [wordValue, U64.max_eq]; omega)
  rw [wordValue] at squareValue
  have pricedSquare : square degree = .ok (.Ok squareWord) := by
    simp only [square, numberCall, bind_ok, CoreOpsTry.branch, squareCall]
  obtain ⟨twice, twiceCall, twiceValue⟩ := mul_normal 2#u64 word (by
    change 2 * word.val ≤ U64.max
    rw [wordValue, U64.max_eq]
    omega)
  change twice.val = 2 * word.val at twiceValue
  rw [wordValue] at twiceValue
  obtain ⟨tripleSquare, tripleSquareCall, tripleSquareValue⟩ := mul_normal 3#u64 squareWord (by
    change 3 * squareWord.val ≤ U64.max
    rw [squareValue, U64.max_eq]
    omega)
  change tripleSquare.val = 3 * squareWord.val at tripleSquareValue
  rw [squareValue] at tripleSquareValue
  obtain ⟨modSquare, modSquareCall, modSquareValue⟩ := add_normal tripleSquare twice (by
    rw [tripleSquareValue, twiceValue, U64.max_eq]
    omega)
  rw [tripleSquareValue, twiceValue] at modSquareValue
  have pricedSquareMod : square_mod degree = .ok (.Ok modSquare) := by
    simp only [square_mod, pricedSquare, bind_ok, CoreOpsTry.branch, tripleSquareCall, numberCall,
      twiceCall, modSquareCall]
  obtain ⟨width, widthCall, widthValue⟩ := add_normal word 1#u64 (by
    change word.val + 1 ≤ U64.max
    rw [wordValue, U64.max_eq]
    omega)
  change width.val = word.val + 1 at widthValue
  rw [wordValue] at widthValue
  obtain ⟨widthSquare, widthSquareCall, widthSquareValue⟩ := mul_normal width width (by rw [widthValue, U64.max_eq]; omega)
  rw [widthValue] at widthSquareValue
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨large, largeCall, largeValue⟩ := mul_normal 8#u64 squareWord (by
      change 8 * squareWord.val ≤ U64.max
      rw [squareValue, U64.max_eq]
      omega)
    change large.val = 8 * squareWord.val at largeValue
    rw [squareValue] at largeValue
    obtain ⟨total, totalCall, totalValue⟩ := add_normal large twice (by
      rw [largeValue, twiceValue, U64.max_eq]
      omega)
    refine ⟨total, ?_, ?_⟩
    · simp only [WorkScheduleV1.cost, pricedSquare, bind_ok, CoreOpsTry.branch, largeCall, numberCall,
        twiceCall, totalCall]
    · rw [totalValue, largeValue, twiceValue, tableUnits]
      ring
  · obtain ⟨withMargin, marginCall, marginValue⟩ := add_normal modSquare 2#u64 (by
      change modSquare.val + 2 ≤ U64.max
      rw [modSquareValue, U64.max_eq]
      omega)
    change withMargin.val = modSquare.val + 2 at marginValue
    rw [modSquareValue] at marginValue
    obtain ⟨total, totalCall, totalValue⟩ := mul_normal 63#u64 withMargin (by
      change 63 * withMargin.val ≤ U64.max
      rw [marginValue, U64.max_eq]
      omega)
    refine ⟨total, ?_, ?_⟩
    · simp only [WorkScheduleV1.cost, pricedSquareMod, bind_ok, CoreOpsTry.branch, marginCall, totalCall]
    · change total.val = 63 * (3 * d * d + 2 * d + 2)
      change total.val = 63 * withMargin.val at totalValue
      rw [totalValue, marginValue]
      ring
  · obtain ⟨total, totalCall, totalValue⟩ := add_normal modSquare width (by
      rw [modSquareValue, widthValue, U64.max_eq]
      omega)
    refine ⟨total, ?_, ?_⟩
    · simp only [WorkScheduleV1.cost, pricedSquareMod, bind_ok, CoreOpsTry.branch, numberCall,
        widthCall, totalCall]
    · rw [totalValue, modSquareValue, widthValue, splitCheckUnits, squareUnits]
      ring
  · obtain ⟨quadratic, quadraticCall, quadraticValue⟩ := mul_normal 8#u64 widthSquare (by
      change 8 * widthSquare.val ≤ U64.max
      rw [widthSquareValue, U64.max_eq]
      omega)
    change quadratic.val = 8 * widthSquare.val at quadraticValue
    rw [widthSquareValue] at quadraticValue
    obtain ⟨linear, linearCall, linearValue⟩ := mul_normal 128#u64 width (by
      change 128 * width.val ≤ U64.max
      rw [widthValue, U64.max_eq]
      omega)
    change linear.val = 128 * width.val at linearValue
    rw [widthValue] at linearValue
    obtain ⟨total, totalCall, totalValue⟩ := add_normal quadratic linear (by
      rw [quadraticValue, linearValue, U64.max_eq]
      omega)
    refine ⟨total, ?_, ?_⟩
    · simp only [WorkScheduleV1.cost, numberCall, bind_ok, CoreOpsTry.branch, widthCall,
        widthSquareCall, quadraticCall, linearCall, totalCall]
    · rw [totalValue, quadraticValue, linearValue, gcdUnits]
      ring
  · obtain ⟨quadratic, quadraticCall, quadraticValue⟩ := mul_normal 4#u64 widthSquare (by
      change 4 * widthSquare.val ≤ U64.max
      rw [widthSquareValue, U64.max_eq]
      omega)
    change quadratic.val = 4 * widthSquare.val at quadraticValue
    rw [widthSquareValue] at quadraticValue
    obtain ⟨total, totalCall, totalValue⟩ := add_normal quadratic 128#u64 (by
      change quadratic.val + 128 ≤ U64.max
      rw [quadraticValue, U64.max_eq]
      omega)
    refine ⟨total, ?_, ?_⟩
    · simp only [WorkScheduleV1.cost, numberCall, bind_ok, CoreOpsTry.branch, widthCall,
        widthSquareCall, quadraticCall, totalCall]
    · change total.val = 4 * (d + 1) ^ 2 + 128
      change total.val = quadratic.val + 128 at totalValue
      rw [totalValue, quadraticValue]
      ring
  · obtain ⟨total, totalCall, totalValue⟩ := mul_normal 4#u64 width (by
      change 4 * width.val ≤ U64.max
      rw [widthValue, U64.max_eq]
      omega)
    refine ⟨total, ?_, ?_⟩
    · simp only [WorkScheduleV1.cost, numberCall, bind_ok, CoreOpsTry.branch, widthCall, totalCall]
    · change total.val = 4 * (d + 1)
      change total.val = 4 * width.val at totalValue
      rwa [widthValue] at totalValue

/-- Exact original V1 leaf costs at the three admitted degrees,
    including the zero-degree terminal path. -/
def ActualNativeRootLeafPrice : Prop :=
  ∀ degree : Usize, degree.val ≤ 2 →
    ∃ units : U64, WorkScheduleV1.cost (.Leaf degree) = .ok (.Ok units) ∧
      units.val = (if degree.val = 0 then 0 else if degree.val = 1 then 1 else 160) ∧
      units.val ≤ 160 * degree.val

theorem native_root_leaf_price : ActualNativeRootLeafPrice := by
  intro degree bounded
  have possibilities : degree.val = 0 ∨ degree.val = 1 ∨ degree.val = 2 := by omega
  rcases possibilities with zero | one | two
  · have exactDegree : degree = 0#usize := UScalar.eq_of_val_eq zero
    subst degree
    exact ⟨0#u64, rfl, rfl, by decide⟩
  · have exactDegree : degree = 1#usize := UScalar.eq_of_val_eq one
    subst degree
    exact ⟨1#u64, rfl, rfl, by decide⟩
  · have exactDegree : degree = 2#usize := UScalar.eq_of_val_eq two
    subst degree
    exact ⟨160#u64, rfl, rfl, by decide⟩

#print axioms native_root_leaf_price
#print axioms native_root_node_prices
#print axioms native_roots_bound
#print axioms native_proper_factor_tree_budget

end BulksketchBridge.RootWorkBudget
