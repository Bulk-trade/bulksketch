import BulksketchBridge.AffineSplitter
import BulksketchBridge.AffineSubspacesAnnihilators

namespace BulksketchBridge.AffineSplitter

open Aeneas Aeneas.Std DenseCoefficient RebuiltLfsr BmEntry SliceKernels Algebra.Gf64 Polynomial
open DenseReducerAlgebra DenseReducerSquare DenseMulConvolutionSpec
open bulksketch.backend.contract
open scoped BigOperators DenseMulReductionSpec

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def FullSquareLaw {K : Type} (square : Square) (kernels : BulkKernels K bulksketch.field.Gf64)
    (modulus table : Slice U64) (degree : Nat) : Prop :=
  ∀ input dst raw, input.length ≤ degree → degree ≤ dst.length → 2 * degree < raw.length →
    ∃ size squared scratch,
      square fieldDictionary kernels input modulus table dst raw = .ok (size, squared, scratch) ∧
      squared.length = dst.length ∧ scratch.length = raw.length ∧
      slicePolynomial (prefixSlice squared degree) = (slicePolynomial input ^ 2) %ₘ slicePolynomial modulus

theorem native_full_square {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (rawLaw : RawMulAgrees kernels) (squareLaw : SquareAgrees kernels) (reduceLaw : DenseMul.reduceAgrees kernels)
    (modulus table : Slice U64) (degree : Nat)
    (minimum : 4 ≤ modulus.length) (shape : modulus.length = degree + 1) (monic : modulus[degree]! = 1#u64)
    (tableLen : table.length = degree * (degree / 2)) (correct : CorrectTable modulus table degree)
    (backend : BackendSquareLaw kernels modulus table degree) :
    FullSquareLaw RootTrace.nativeSquare kernels modulus table degree := by
  intro input dst raw inputRoom dstRoom rawRoom
  obtain ⟨size, squared, scratch, normal, _, squaredLen, scratchLen, represented⟩ :=
    native_modular_square kernels rawLaw squareLaw reduceLaw modulus table degree minimum shape monic
      tableLen correct backend input dst raw inputRoom dstRoom rawRoom
  obtain ⟨accelerated, active, returned, called, _, returnedLen, _⟩ :=
    backend input (prefixSlice dst degree) raw inputRoom
      (by rw [prefix_length, Nat.min_eq_left dstRoom]) rawRoom
  have sourceDegree : modulus.length - 1 = degree := by omega
  have modeled := square_mod_into_refines kernels rawLaw squareLaw reduceLaw input modulus table dst raw
    minimum (by rwa [sourceDegree]) (by rwa [sourceDegree]) (by rwa [sourceDegree])
    (by rwa [sourceDegree]) (by rwa [sourceDegree]) accelerated active returned
    (by rwa [sourceDegree]) (by rw [sourceDegree, returnedLen]; omega)
  rw [sourceDegree] at modeled
  have exactOutput := Result.ok_injective (normal.symm.trans modeled)
  have sizeEq : size = outputLength squared degree := by
    rw [show size = (expectedOutput input table dst active returned degree accelerated).1 from congrArg Prod.fst exactOutput,
      show squared = (expectedOutput input table dst active returned degree accelerated).2.1 from
        congrArg (fun result => result.2.1) exactOutput]
    cases accelerated <;> rfl
  have lengthValue : size.val = DenseNormalization.normalizedLength (squared.val.take degree) := by
    rw [sizeEq]
    simp only [outputLength, prefixSlice, Slice.from_val]
    exact ClosedLeafAdvance.word_val _
      ((DenseNormalization.normalizedLength_le _).trans
        ((List.length_take_le _ _).trans (dstRoom.trans dst.length_ineq)))
  refine ⟨size, squared, scratch, normal, squaredLen, scratchLen, ?_⟩
  rw [lengthValue, normalized_prefix_polynomial squared degree (by omega)] at represented
  exact represented

private theorem scale_polynomial (dst source output : Slice U64) (scale : U64)
    (same : dst.length = source.length) (outputLen : output.length = dst.length)
    (words : ∀ i < dst.length, output[i]! = dst[i]! ^^^ (⟨multiplyWord scale.bv source[i]!.bv⟩ : U64)) :
    slicePolynomial output = slicePolynomial dst + C (toField scale.bv) * slicePolynomial source := by
  ext i
  rw [coeff_add, coeff_C_mul, slicePolynomial_coeff, slicePolynomial_coeff, slicePolynomial_coeff, outputLen, ← same]
  by_cases active : i < dst.length
  · simp only [active, ite_true, words i active]
    exact (toField_xor _ _).trans (congrArg (toField dst[i]!.bv + ·) (toField_mul _ _))
  · simp only [active, ite_false, mul_zero, add_zero]

private theorem restored_prefix (dst replacement : Slice U64) (degree : Nat)
    (width : replacement.length = degree) (room : degree ≤ dst.length) :
    prefixSlice (restorePrefix dst replacement) degree = replacement := by
  apply Slice.ext
  have replacementRoom : replacement.val.length ≤ dst.val.length := by
    change replacement.length ≤ dst.length
    omega
  have wordCount : replacement.val.length = degree := width
  simp only [prefixSlice, restorePrefix, Slice.from_val, List.setSlice!, Nat.sub_zero, Nat.zero_add,
    List.take_zero, List.nil_append, Nat.min_eq_left replacementRoom, List.take_length]
  rw [← wordCount, List.take_left]

private theorem eval_remainder (p f : Polynomial Field) (point : Field) (root : f.IsRoot point) :
    (p %ₘ f).eval point = p.eval point := by
  change f.eval point = 0 at root
  have h := congrArg (Polynomial.eval point) (modByMonic_add_div p f)
  simpa only [eval_add, eval_mul, root, zero_mul, add_zero] using h

noncomputable def linearTerms : List U64 → Field → Field
  | [], _ => 0
  | coefficient :: rest, value => toField coefficient.bv * value + linearTerms rest (value ^ 2)

theorem linearTerms_sum (coefficients : List U64) (value : Field) :
    linearTerms coefficients value =
      ∑ i ∈ Finset.range coefficients.length, toField coefficients[i]!.bv * value ^ (2 ^ i) := by
  induction coefficients generalizing value with
  | nil => simp [linearTerms]
  | cons coefficient rest ih =>
    simp only [linearTerms, ih, List.length_cons, Finset.sum_range_succ',
      List.getElem!_cons_zero, pow_zero, pow_one, List.getElem!_cons_succ]
    rw [add_comm]
    apply congrArg (fun total : Field => total + toField coefficient.bv * value)
    apply Finset.sum_congr rfl
    intro i _
    rw [← pow_mul, pow_succ']

private theorem prefix_full (words : Slice U64) (degree : Nat) (width : words.length = degree) :
    prefixSlice words degree = words := by
  apply Slice.ext
  simp only [prefixSlice, Slice.from_val]
  exact List.take_of_length_le width.le

theorem fold_evaluates {K : Type} (square : Square) (kernels : BulkKernels K bulksketch.field.Gf64)
    (modulus table : Slice U64) (degree rawLength : Nat) (rawRoom : 2 * degree < rawLength)
    (scale : TimesXMod.ExactScaleXor kernels) (squareLaw : FullSquareLaw square kernels modulus table degree)
    (coefficients : List U64) (initial : State) (admitted : Admitted degree rawLength initial) :
    ∃ final, fold square fieldDictionary kernels modulus table degree coefficients initial = .ok final ∧
      Admitted degree rawLength final ∧ final.1.length = initial.1.length ∧
      ∀ point : Field, (slicePolynomial modulus).IsRoot point →
        (slicePolynomial (prefixSlice final.1 degree)).eval point =
          (slicePolynomial (prefixSlice initial.1 degree)).eval point +
            linearTerms coefficients ((slicePolynomial initial.2.2.1).eval point) := by
  induction coefficients generalizing initial with
  | nil => exact ⟨initial, rfl, admitted, rfl, fun _ _ => (add_zero _).symm⟩
  | cons coefficient rest ih =>
    obtain ⟨output, raw, residue, squared⟩ := initial
    obtain ⟨outputRoom, rawSize, residueSize, squaredSize⟩ := admitted
    change degree ≤ output.length at outputRoom
    change raw.length = rawLength at rawSize
    change residue.length = degree at residueSize
    change squared.length = degree at squaredSize
    let active := prefixSlice output degree
    have activeSize : active.length = degree := by
      rw [show active = prefixSlice output degree from rfl, prefix_length, Nat.min_eq_left outputRoom]
    obtain ⟨scaled, scaleNormal, scaleSize, scaleWords⟩ :=
      scale active residue coefficient (activeSize.trans residueSize.symm)
    let nextOutput := restorePrefix output scaled
    have nextOutputSize : nextOutput.length = output.length := restore_length _ _
    have nextOutputRoom : degree ≤ nextOutput.length := by rwa [nextOutputSize]
    have outputRep : slicePolynomial (prefixSlice nextOutput degree) =
        slicePolynomial active + C (toField coefficient.bv) * slicePolynomial residue := by
      rw [restored_prefix output scaled degree (scaleSize.trans activeSize) outputRoom]
      exact scale_polynomial active residue scaled coefficient
        (activeSize.trans residueSize.symm) scaleSize scaleWords
    cases rest with
    | nil =>
      have stepped : step square fieldDictionary kernels modulus table degree coefficient false
          (output, raw, residue, squared) = .ok (nextOutput, raw, residue, squared) := by
        unfold step
        dsimp! only
        have scaleEq : kernels.ArithmeticInst.scale_xor (prefixSlice output degree) residue coefficient =
            .ok scaled := scaleNormal
        simp only [scaleEq, bind_ok, Bool.false_eq_true, ite_false, nextOutput]
      refine ⟨(nextOutput, raw, residue, squared), ?_, ⟨nextOutputRoom, rawSize, residueSize, squaredSize⟩, nextOutputSize, ?_⟩
      · simp only [fold, List.isEmpty_nil, Bool.not_true, stepped, bind_ok]
      · intro point _
        rw [outputRep, eval_add, eval_mul, eval_C]
        simp [linearTerms, active]
    | cons nextCoefficient rest =>
      obtain ⟨_, nextSquare, nextRaw, squareNormal, nextSquareLen, nextRawLen, squareRep⟩ :=
        squareLaw residue squared raw residueSize.le squaredSize.ge (by omega)
      have nextSquareWidth := nextSquareLen.trans squaredSize
      have copy := ClosedLeaf.copy_normal residue nextSquare (residueSize.trans nextSquareWidth.symm)
      let next : State := (nextOutput, nextRaw, nextSquare, nextSquare)
      obtain ⟨final, normal, fitted, finalWidth, evaluation⟩ := ih next
        ⟨nextOutputRoom, nextRawLen.trans rawSize, nextSquareWidth, nextSquareWidth⟩
      refine ⟨final, ?_, fitted, finalWidth.trans nextOutputSize, ?_⟩
      · have stepped : step square fieldDictionary kernels modulus table degree coefficient true
            (output, raw, residue, squared) = .ok next := by
          unfold step
          dsimp! only
          have scaleEq : kernels.ArithmeticInst.scale_xor (prefixSlice output degree) residue coefficient =
              .ok scaled := scaleNormal
          simp only [scaleEq, bind_ok, ite_true, squareNormal, next, nextOutput]
          dsimp! only
          simp only [copy, bind_ok]
        unfold fold
        simp only [List.isEmpty_cons, Bool.not_false, stepped, bind_ok]
        exact normal
      · intro point root
        have squareValue : (slicePolynomial nextSquare).eval point = (slicePolynomial residue).eval point ^ 2 := by
          rw [← prefix_full nextSquare degree nextSquareWidth, squareRep, eval_remainder _ _ _ root, eval_pow]
        rw [evaluation point root]
        change (slicePolynomial (prefixSlice nextOutput degree)).eval point +
          linearTerms (nextCoefficient :: rest) ((slicePolynomial nextSquare).eval point) = _
        rw [outputRep, eval_add, eval_mul, eval_C, squareValue, add_assoc]
        rfl

private theorem initialized_monomial (shape : Slice U64) (index : Nat) (word : U64)
    (inside : index < shape.length) :
    slicePolynomial ((zeroWords shape).setAtNat index word) = monomial index (toField word.bv) := by
  ext i
  rw [slicePolynomial_coeff, Slice.setAtNat_length, zero_length, coeff_monomial]
  by_cases same : index = i
  · subst i
    rw [ite_eq_left inside, ite_eq_left rfl, Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_eq]
    rwa [zero_length]
  · rw [ite_eq_right same]
    by_cases active : i < shape.length
    · rw [ite_eq_left active, Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_ne _ _ _ _ same]
      simp only [zeroWords, Slice.from_val, List.getElem!_replicate, active]
      exact toField_zero
    · rw [ite_eq_right active]

private theorem prefix_update (words : Slice U64) (count index : Nat) (word : U64) :
    prefixSlice (words.setAtNat index word) count = (prefixSlice words count).setAtNat index word := by
  apply Slice.ext
  simp only [prefixSlice, Slice.setAtNat, Slice.from_val, List.take_set]

private theorem initial_polynomials (degree : Nat) (base : U64) (output work : Slice U64)
    (raw : Slice bulksketch.types.RawProduct) (positive : 2 ≤ degree)
    (outputRoom : degree ≤ output.length) (workRoom : 2 * degree ≤ work.length) :
    let initial := initialState degree base output work raw
    Admitted degree raw.length initial ∧
      slicePolynomial (prefixSlice initial.1 degree) = C (toField base.bv) ∧
      slicePolynomial initial.2.2.1 = X := by
  have outPrefix : (prefixSlice output degree).length = degree := by
    rw [prefix_length, Nat.min_eq_left outputRoom]
  have workPrefix : (prefixSlice work degree).length = degree := by
    rw [prefix_length, Nat.min_eq_left (by omega)]
  have tailWidth : (prefixSlice (tail work degree) degree).length = degree := by
    rw [prefix_length, tail_length, Nat.min_eq_left (by omega)]
  have outputLen : (restorePrefix output (zeroWords (prefixSlice output degree))).length = output.length :=
    restore_length _ _
  refine ⟨⟨?_, rfl, ?_, tailWidth⟩, ?_, ?_⟩
  · change degree ≤ ((restorePrefix output (zeroWords (prefixSlice output degree))).setAtNat 0 base).length
    rwa [Slice.setAtNat_length, outputLen]
  · change ((zeroWords (prefixSlice work degree)).setAtNat 1 1#u64).length = degree
    rw [Slice.setAtNat_length, zero_length, workPrefix]
  · change slicePolynomial (prefixSlice
      ((restorePrefix output (zeroWords (prefixSlice output degree))).setAtNat 0 base) degree) = _
    rw [prefix_update,
      restored_prefix output (zeroWords (prefixSlice output degree)) degree (by rw [zero_length, outPrefix]) outputRoom,
      initialized_monomial _ 0 base (by omega), ← C_mul_X_pow_eq_monomial, pow_zero, mul_one]
  · change slicePolynomial ((zeroWords (prefixSlice work degree)).setAtNat 1 1#u64) = _
    have oneWord : toField (1#u64).bv = 1 := toField_one
    rw [initialized_monomial _ 1 1#u64 (by omega), ← C_mul_X_pow_eq_monomial, oneWord, map_one, one_mul, pow_one]

theorem native_splitter_at_roots {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (rawLaw : RawMulAgrees kernels) (squareLaw : SquareAgrees kernels) (reduceLaw : DenseMul.reduceAgrees kernels)
    (arithmetic : AffineLinearEval.CorrectArithmetic kernels) (scale : TimesXMod.ExactScaleXor kernels)
    (modulus table linear : Slice U64) (base : U64) (output work : Slice U64)
    (raw : Slice bulksketch.types.RawProduct) (degree : Nat)
    (shape : modulus.length = degree + 1) (minimum : 4 ≤ modulus.length)
    (outputRoom : degree ≤ output.length) (workRoom : 2 * degree ≤ work.length) (rawRoom : 2 * degree < raw.length)
    (monic : modulus[degree]! = 1#u64) (tableLen : table.length = degree * (degree / 2))
    (tableCorrect : CorrectTable modulus table degree) (backend : BackendSquareLaw kernels modulus table degree) :
    ∃ normalized trace newWork newRaw,
      bulksketch.decode.affine.splitter RootTrace.nativeSquare fieldDictionary kernels modulus table linear base
        output work raw = .ok (normalized, trace, newWork, newRaw) ∧
      normalized.val ≤ degree ∧ DenseGcd.Normal (prefixSlice trace normalized.val) ∧
      trace.length = output.length ∧ newWork.length = work.length ∧ newRaw.length = raw.length ∧
      ∀ point : Field, (slicePolynomial modulus).IsRoot point →
        (slicePolynomial (prefixSlice trace normalized.val)).eval point =
          (AffineSubspaces.rowPolynomial linear).eval point +
            (AffineSubspaces.rowPolynomial linear).eval (toField base.bv) := by
  obtain ⟨evaluated, final, normalized, evaluation, folded, fitted, normLen, ran⟩ :=
    native_splitter_refines kernels modulus table linear base output work raw degree shape minimum
      outputRoom workRoom rawRoom monic tableLen tableCorrect backend arithmetic scale rawLaw squareLaw reduceLaw
  obtain ⟨initialFit, outputRep, residueRep⟩ :=
    initial_polynomials degree evaluated output work raw (by omega) outputRoom workRoom
  obtain ⟨final', modeled, _, finalWidth, atRoots⟩ := fold_evaluates RootTrace.nativeSquare kernels modulus table degree
    raw.length rawRoom scale
    (native_full_square kernels rawLaw squareLaw reduceLaw modulus table degree minimum shape monic tableLen tableCorrect backend)
    linear.val (initialState degree evaluated output work raw) initialFit
  have finalEq := Result.ok_injective (modeled.symm.trans folded)
  subst final'
  have normLen' : normalized.val = DenseNormalization.normalizedLength (final.1.val.take degree) := by
    simpa only [prefixSlice, Slice.from_val] using normLen
  have outputLen := DenseDivision.output_length_normal final.1 degree fitted.1
  dsimp only at outputLen
  rw [DenseDivision.normalized_value _ _ fitted.1, ← normLen'] at outputLen
  have normalizedPrefix : DenseGcd.Normal (prefixSlice final.1 normalized.val) := by
    have count : (prefixSlice final.1 normalized.val).length = normalized.val := by
      rw [prefix_length, Nat.min_eq_left (outputLen.1.trans fitted.1)]
    intro nonempty
    rw [count] at nonempty ⊢
    exact outputLen.2 nonempty
  have width : final.1.length = output.length := by
    rw [finalWidth]
    simp only [initialState, Slice.setAtNat_length, restore_length]
  refine ⟨normalized, final.1, _, _, ran, outputLen.1, normalizedPrefix, width, splitBack_length .., fitted.2.1, ?_⟩
  intro point root
  have linearAt : linearTerms linear.val point = (AffineSubspaces.rowPolynomial linear).eval point := by
    rw [linearTerms_sum]
    simp only [AffineSubspaces.rowPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
      Slice.getElem!_Nat_eq, Slice.length]
  rw [normLen', normalized_prefix_polynomial final.1 degree fitted.1,
    atRoots point root, outputRep, residueRep, eval_C, eval_X, linearAt, evaluation,
    AffineSubspaces.rowPolynomial_eval, add_comm]

open AffineSubspaces AffineSubspaceAlgebra in
/-- Build the original table and split using its rank row. At a root of the
    current factor in the parent coset, a zero chooses the first child and a
    nonzero chooses the translated child. -/
def ActualNativeSplitterChildren : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    AffineLinearEval.CorrectArithmetic kernels → TimesXMod.ExactScaleXor kernels →
    ∀ (modulus table basis subspaceTable : Slice U64) (base : U64) (output work : Slice U64)
      (raw : Slice bulksketch.types.RawProduct) (degree rank : Nat),
    modulus.length = degree + 1 → 4 ≤ modulus.length →
    degree ≤ output.length → 2 * degree ≤ work.length → 2 * degree < raw.length →
    modulus[degree]! = 1#u64 → table.length = degree * (degree / 2) →
    CorrectTable modulus table degree → BackendSquareLaw kernels modulus table degree →
    basis.length ≤ 64 → offset (basis.length + 1) ≤ subspaceTable.length →
    rank < basis.length →
    toField basis[rank]!.bv ∉ spanWords (prefixDirections basis rank) →
    ∃ filled normalized trace newWork newRaw,
      bulksketch.decode.affine.subspaces fieldDictionary kernels basis subspaceTable = .ok filled ∧
      bulksketch.decode.affine.splitter RootTrace.nativeSquare fieldDictionary kernels modulus table
        (row filled rank) base output work raw = .ok (normalized, trace, newWork, newRaw) ∧
      ∀ point : Field, (slicePolynomial modulus).IsRoot point →
        point ∈ coset (toField base.bv) (prefixDirections basis (rank + 1)) →
        let value := (slicePolynomial (prefixSlice trace normalized.val)).eval point
        (value = 0 ↔ point ∈ coset (toField base.bv) (prefixDirections basis rank)) ∧
        (value ≠ 0 ↔ point ∈ coset (toField base.bv + toField basis[rank]!.bv) (prefixDirections basis rank))

open AffineSubspaces AffineSubspaceAlgebra in
theorem native_splitter_children : ActualNativeSplitterChildren := by
  intro K kernels rawLaw squareLaw reduceLaw arithmetic scale modulus table basis subspaceTable base output work raw
    degree rank shape minimum outputRoom workRoom rawRoom monic tableLen tableCorrect backend rankBound subspaceRoom
    active independent
  let _ : CharP Field 2 := charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2
  obtain ⟨filled, tableNormal, _, exactRows⟩ :=
    subspaces_annihilators kernels arithmetic basis subspaceTable rankBound subspaceRoom
  obtain ⟨normalized, trace, newWork, newRaw, splitNormal, _, _, _, _, _, evaluated⟩ :=
    native_splitter_at_roots kernels rawLaw squareLaw reduceLaw arithmetic scale modulus table (row filled rank)
      base output work raw degree shape minimum outputRoom workRoom rawRoom monic tableLen tableCorrect backend
  refine ⟨filled, normalized, trace, newWork, newRaw, tableNormal, splitNormal, ?_⟩
  intro point root parent
  dsimp only
  have left : (slicePolynomial (prefixSlice trace normalized.val)).eval point = 0 ↔
      point ∈ coset (toField base.bv) (prefixDirections basis rank) := by
    rw [evaluated point root, exactRows rank active.le]
    simpa only [AffineSubspaceAlgebra.splitter, eval_add, eval_C] using
      splitter_zero (toField base.bv) point (prefixDirections basis rank)
  have children := (coset_children (toField base.bv) (toField basis[rank]!.bv) point
    (prefixDirections basis rank)).mp parent
  have disjoint := children_disjoint (toField base.bv) (toField basis[rank]!.bv)
    (prefixDirections basis rank) independent
  refine ⟨left, ?_⟩
  constructor
  · intro nonzero
    exact children.resolve_left (fun member => nonzero (left.mpr member))
  · intro right vanishes
    exact Set.disjoint_left.mp disjoint (left.mp vanishes) right

end BulksketchBridge.AffineSplitter
