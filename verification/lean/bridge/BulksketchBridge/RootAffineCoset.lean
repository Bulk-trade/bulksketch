import BulksketchBridge.RootAffineAdmission
import BulksketchBridge.RootAffineFactorFiber
import BulksketchBridge.RootWorkspaceBudget
import BulksketchBridge.AffineSelector
import Mathlib.FieldTheory.Separable

namespace BulksketchBridge.RootAffinePreparation

open Aeneas Aeneas.Std DenseCoefficient RebuiltLfsr BmEntry Polynomial Algebra.Gf64 AffineEnumerate
open DenseReducerAlgebra DenseReducerSquare AffineSubspaceAlgebra AffineSubspaces SliceKernels
open AffineLinearEval (CorrectArithmetic)
open RootRun (affinePreparationCost affine_preparation_cost_refines roots_charge_returns)
open bulksketch.backend.contract bulksketch.decode.affine bulksketch.decode.roots
open bulksketch.decode.scratch bulksketch.decode.roots.Roots bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem tail_set_full (words replacement : Slice U64) (offset : Nat)
    (bound : offset ≤ words.length) (width : replacement.length = words.length - offset) :
    tail (words.setSlice! offset replacement.val) offset = replacement := by
  apply Slice.ext
  change offset ≤ words.val.length at bound
  change replacement.val.length = words.val.length - offset at width
  simp only [tail, Slice.from_val, Slice.setSlice!_val, List.setSlice!, ← width,
    Nat.min_self, List.take_length, List.append_assoc]
  have dropRest : List.drop (offset + replacement.val.length) words.val = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  rw [dropRest, List.append_nil, List.drop_append, List.length_take, Nat.min_eq_left bound,
    Nat.sub_self, List.drop_zero, List.drop_eq_nil_iff.mpr (by simp [List.length_take, bound]), List.nil_append]

/-- With the input factor split and simple, the original affine stage
    prepares a complete factor coset after the charge succeeds. Minimality
    excludes the zero-X guard and the full solve-map fiber excludes both
    rank rejections. -/
def ActualNativePreparationCoset : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter paid : WorkMeter) (capacity budget : Nat),
    NativeArena kernels roots workspace → RootRun.BudgetBuffers workspace capacity budget →
    roots.degree.val ≤ budget → roots.stride.val ≤ budget + 1 →
    TimesXMod.ExactScaleXor kernels → DenseDivRem.MulWordLaw kernels →
    BmTerminal.NativeInverse kernels → DenseMulConvolutionSpec.RawMulAgrees kernels →
    SquareAgrees kernels → DenseMul.reduceAgrees kernels → CorrectArithmetic kernels →
    charge meter (.AffinePreparation roots.degree) = .ok (.Ok (), paid) →
    let factor := slicePolynomial (prefixSlice workspace.polynomials (roots.degree.val + 1))
    factor.Splits → factor.roots.Nodup →
    (∃ (stage : Stage) (base : U64) (rank : Usize) (directions : Array U64 64#usize) (written : RowWorkspace),
      (stage = .AffineEnumeration ∨ stage = .AffineSplit) ∧
      Roots.prepare_affine RootRun.nativeCalls.preparation dictionary kernels roots workspace meter =
        .ok (.Ok (.Ok stage), { roots with affine_ready := true, affine_base := base, affine_rank := rank },
          written, id, paid) ∧
      written.basis.directions = some directions ∧ written.basis.len = UScalar.cast .U32 rank ∧
      let basis := prefixSlice directions.to_slice rank.val
      rank.val ≤ roots.degree.val ∧ basis.length = rank.val ∧ IndependentDirections basis ∧
      written.polynomials = workspace.polynomials ∧
      (stage = .AffineSplit → ExactThrough basis (tail written.factors (roots.stride.val * roots.stride.val)) rank.val) ∧
      ∀ point, factor.IsRoot point → point ∈ coset (toField base.bv) (prefixDirections basis basis.length))

theorem native_preparation_coset : ActualNativePreparationCoset := by
  intro K kernels roots workspace meter paid capacity budget arena sized degreeBudget stride
    scale mul inverse rawMul square reduce subspaceArithmetic charged factor split simple
  rw [native_preparation_refines kernels roots workspace meter arena scale mul inverse rawMul square reduce]
  obtain ⟨size, factors, coefficients, work, raw, normal, sizePos, sizeBound, factorWidth, coeffWidth, witnessMonic, divides, squarefreeX⟩ :=
    native_multiple_from_arena kernels roots workspace arena scale mul inverse rawMul square reduce
  have paidModel : StageCharge.chargeResult meter (affinePreparationCost roots.degree) = (.Ok (), paid) := by
    have exactCharge := roots_charge_returns meter (.AffinePreparation roots.degree)
      (affinePreparationCost roots.degree) (affine_preparation_cost_refines roots.degree)
    rw [charged] at exactCharge
    exact Result.ok.injEq.mp exactCharge.symm
  let words := prefixSlice coefficients size.val
  let linear := tail words 1
  have wordsLen : words.length = size.val := by
    dsimp only [words]
    rw [prefix_length, Nat.min_eq_left (by omega)]
  have factorLen : (prefixSlice workspace.polynomials (roots.degree.val + 1)).length = roots.degree.val + 1 := by
    rw [prefix_length, Nat.min_eq_left (by have := arena.polynomialRoom; omega)]
  have factorLead : (prefixSlice workspace.polynomials (roots.degree.val + 1))[roots.degree.val]! = 1#u64 := by
    simp only [prefixSlice, Slice.getElem!_Nat_eq, Slice.from_val, List.getElem!_eq_getElem?_getD,
      List.getElem?_take_of_lt (Nat.lt_succ_self roots.degree.val)]
    simpa only [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD] using arena.monic
  obtain ⟨factorMonic, factorDegree⟩ :=
    modulus_monic (prefixSlice workspace.polynomials (roots.degree.val + 1)) roots.degree.val factorLen factorLead
  have squarefree : Squarefree factor :=
    ((nodup_roots_iff_of_splits factorMonic.ne_zero split).mp simple).squarefree
  have zero : coefficients[(1 : Nat)]! ≠ 0#u64 := squarefreeX squarefree
  have degree : factor.natDegree = roots.degree.val := natDegree_eq_of_degree_eq_some factorDegree
  have degreePos : 0 < factor.natDegree := by rw [degree]; have := arena.degreeMin; omega
  have sizeTwo : 2 ≤ size.val := by
    by_contra! tooShort
    have sizeOne : size.val = 1 := by omega
    have empty : linear.length = 0 := by rw [tail_length, wordsLen, sizeOne]
    have vanishes : rowPolynomial linear = 0 := by simp only [rowPolynomial, empty, Finset.range_zero, Finset.sum_empty]
    change factor ∣ AffineMultiple.witnessPolynomial words[0]! linear at divides
    have constant : AffineMultiple.witnessPolynomial words[0]! linear = C (toField words[0]!.bv) := by
      simp only [AffineMultiple.witnessPolynomial, vanishes, add_zero]
    change (AffineMultiple.witnessPolynomial words[0]! linear).Monic at witnessMonic
    rw [constant] at divides witnessMonic
    have small := natDegree_le_of_dvd divides witnessMonic.ne_zero
    rw [natDegree_C] at small
    omega
  have hasX : 0 < linear.length := by rw [tail_length, wordsLen]; omega
  have wordX : linear[(0 : Nat)]! = coefficients[(1 : Nat)]! := by
    simp only [linear, words, tail, prefixSlice, Slice.getElem!_Nat_eq, Slice.from_val,
      List.getElem!_eq_getElem?_getD, List.getElem?_drop,
      List.getElem?_take_of_lt (by omega : 1 < size.val)]
  obtain ⟨base, rank, directions, mapped, rankBound, basisLen, independent, enough, strict, contains⟩ :=
    native_factor_fiber kernels scale words linear (Array.repeat 64#usize 0#u64) factor
      (by rwa [wordsLen]) (by rw [wordsLen]; have := arena.degreeMax; omega)
      (by simp only [linear, tail, Slice.from_val]) hasX (wordX ▸ zero) degreePos split simple divides
  have mapNormal : mapInput kernels size coefficients = .ok (some (base, rank), directions) := mapped
  have strictRank : ¬ size.val - 1 ≤ rank.val := by rw [wordsLen] at strict; omega
  have enoughPoints : insufficientPoints roots.degree rank = false := by
    rw [degree] at enough
    unfold insufficientPoints
    exact decide_eq_false (fun h => (Nat.not_lt_of_ge enough) h.2)
  have rankDegree : rank.val ≤ roots.degree.val := by rw [wordsLen] at strict; omega
  let basis := prefixSlice directions.to_slice rank.val
  obtain ⟨enumerate, decision⟩ :=
    AffineSelector.enumerate_preferred_returns roots.degree rank arena.degreeMax rankBound
  have shape (stage : Stage) (written : RowWorkspace)
      (choice : stage = .AffineEnumeration ∨ stage = .AffineSplit)
      (ran : expected RootRun.nativeCalls.preparation kernels roots workspace meter =
        .ok (.Ok (.Ok stage), { roots with affine_ready := true, affine_base := base, affine_rank := rank },
          written, id, paid))
      (dirs : written.basis.directions = some directions) (len : written.basis.len = UScalar.cast .U32 rank)
      (polyFrame : written.polynomials = workspace.polynomials)
      (tableFrame : stage = .AffineSplit →
        ExactThrough basis (tail written.factors (roots.stride.val * roots.stride.val)) rank.val) :
      ∃ (stage : Stage) (base : U64) (rank : Usize) (directions : Array U64 64#usize) (written : RowWorkspace),
        (stage = .AffineEnumeration ∨ stage = .AffineSplit) ∧
        expected RootRun.nativeCalls.preparation kernels roots workspace meter =
          .ok (.Ok (.Ok stage), { roots with affine_ready := true, affine_base := base, affine_rank := rank },
            written, id, paid) ∧
        written.basis.directions = some directions ∧ written.basis.len = UScalar.cast .U32 rank ∧
        let basis := prefixSlice directions.to_slice rank.val
        rank.val ≤ roots.degree.val ∧ basis.length = rank.val ∧ IndependentDirections basis ∧
        written.polynomials = workspace.polynomials ∧
        (stage = .AffineSplit → ExactThrough basis (tail written.factors (roots.stride.val * roots.stride.val)) rank.val) ∧
        ∀ point, factor.IsRoot point → point ∈ coset (toField base.bv) (prefixDirections basis basis.length) :=
    ⟨stage, base, rank, directions, written, choice, ran, dirs, len, rankDegree, basisLen, independent, polyFrame, tableFrame, contains⟩
  let prepared : RowWorkspace := {
    workspace with
    bm := splitBack workspace.bm (roots.degree.val + 1) (coefficients, work)
    factors := factors
    raw := raw
    basis := { workspace.basis with directions := some directions, len := UScalar.cast .U32 rank }
  }
  cases enumerate with
  | true =>
    apply shape .AffineEnumeration prepared (Or.inl rfl) _ rfl rfl rfl (fun impossible => by cases impossible)
    simp only [expected, paidModel, normal, bind_ok]
    dsimp! only
    simp only [zero, ite_false, mapNormal, bind_ok]
    dsimp! only
    simp only [strictRank, ite_false, enoughPoints, decision, bind_ok]
    rfl
  | false =>
    let offset := roots.stride.val * roots.stride.val
    have tableRoom := RootRun.subspaces_room_of_budget
      { roots with affine_rank := rank } workspace capacity budget sized stride (rankDegree.trans degreeBudget)
    have tailRoom : AffineSubspaces.offset (basis.length + 1) ≤ (tail factors offset).length := by
      rw [basisLen, tail_length, factorWidth]
      change offset + AffineSubspaces.offset (rank.val + 1) ≤ workspace.factors.length at tableRoom
      omega
    obtain ⟨updated, table, tableWidth, exactRows⟩ :=
      subspaces_annihilators kernels subspaceArithmetic basis (tail factors offset) (by rwa [basisLen]) tailRoom
    have built : subspaces dictionary kernels basis (tail factors offset) = .ok updated := table
    have offsetRoom : offset ≤ factors.length := by
      change offset + AffineSubspaces.offset (rank.val + 1) ≤ workspace.factors.length at tableRoom
      rw [factorWidth]
      omega
    have restored := tail_set_full factors updated offset offsetRoom (tableWidth.trans (tail_length ..))
    have writtenRows : ExactThrough basis (tail (factors.setSlice! offset updated.val) offset) rank.val := by
      rw [restored, ← basisLen]
      exact exactRows
    apply shape .AffineSplit { prepared with factors := factors.setSlice! offset updated.val }
      (Or.inr rfl) _ rfl rfl rfl (fun _ => writtenRows)
    simp only [expected, paidModel, normal, bind_ok]
    dsimp! only
    simp only [zero, ite_false, mapNormal, bind_ok]
    dsimp! only
    simp only [strictRank, ite_false, enoughPoints, decision, bind_ok]
    simp only [Bool.false_eq_true, ite_false]
    rw [built]
    simp only [bind_ok]
    rfl

end BulksketchBridge.RootAffinePreparation
