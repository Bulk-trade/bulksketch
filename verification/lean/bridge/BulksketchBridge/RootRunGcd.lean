import Arithmetic.RootRunGenerated
import BulksketchBridge.DenseGcdAlgebra
import BulksketchBridge.RootSetup
import BulksketchBridge.ClosedLeafAdvance

open Aeneas Aeneas.Std Result Error

namespace BulksketchBridge.RootRun

open BulksketchBridge DenseCoefficient
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1300000

abbrev Reply := core.result.Result (core.result.Result Stage DecodeFailure) DecodeError

def rebuild (workspace : RowWorkspace) (roots : Roots) (buffers : FactorWork) : RowWorkspace :=
  let (polynomials, table, raw, basis) :=
    RootSetup.restoreWork roots.degree.val workspace.polynomials workspace.square_table buffers
  { workspace with polynomials := polynomials, square_table := table, raw := raw, basis := basis }

def basisAt (buffers : FactorWork) (index : Nat) : U64 :=
  match buffers.basis.directions with
  | none => 0#u64
  | some basis => basis.val[index]!

def degree (size : Usize) : Usize := ClosedLeafAdvance.usizeWord (size.val - 1)
def previousRank (roots : Roots) : Usize := ClosedLeafAdvance.usizeWord (roots.affine_rank.val - 1)
def nextDirection (roots : Roots) : U32 := ⟨BitVec.ofNat 32 (roots.direction.val + 1)⟩

def Proper (roots : Roots) (size : Usize) : Prop := 0 < size.val - 1 ∧ size.val - 1 < roots.degree.val

def AfterGcdReady (roots : Roots) (buffers : FactorWork) (size : Usize) : Prop :=
  0 < size.val ∧
    (¬ Proper roots size → roots.affine = true →
      0 < roots.affine_rank.val ∧
      (size = 1#usize → buffers.basis.directions.isSome ∧ roots.affine_rank.val ≤ 64)) ∧
    (¬ Proper roots size → roots.affine = false → roots.direction.val + 1 ≤ U32.max)

def outcome (roots : Roots) (buffers : FactorWork) (size : Usize) : Reply × Roots :=
  let updated := { roots with gcd_len := size, gcd_degree := degree size }
  if 0 < size.val - 1 ∧ size.val - 1 < roots.degree.val then (.Ok (.Ok .FactorDivision), updated)
  else if roots.affine then
    let rank := previousRank roots
    let base := if size = 1#usize then roots.affine_base ^^^ basisAt buffers rank.val else roots.affine_base
    (.Ok (.Ok .AffineSplit), { updated with affine_base := base, affine_rank := rank })
  else
    let direction := nextDirection roots
    (if direction = 64#u32 then .Ok (.Err .NotSplit) else .Ok (.Ok .Trace),
      { updated with direction := direction })

theorem run_gcd_paid (calls : RootRunRuntime.OtherCallees) (division : DenseDivisionRuntime.DivRem)
    {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) (roots : Roots)
    (workspace : RowWorkspace) (meter paidMeter : WorkMeter)
    (polyRoom : 3 * roots.degree.val + 2 ≤ workspace.polynomials.length)
    (tableRoom : RootSetup.tableCount roots.degree.val ≤ workspace.square_table.length)
    (traceRoom : roots.trace_len.val ≤ roots.degree.val)
    (charge : bulksketch.decode.roots.charge meter (.Gcd roots.degree) = .ok (.Ok (), paidMeter))
    (size : Usize) (gcd work : Slice U64) (raw : Slice RawProduct) :
    let buffers := RootSetup.workRegions roots.degree.val workspace.polynomials workspace.square_table workspace.raw workspace.basis
    bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.monic_gcd_into division BmTerminal.fieldDictionary
      kernels buffers.modulus (prefixSlice buffers.trace roots.trace_len.val) buffers.gcd buffers.work buffers.raw =
      .ok (size, gcd, work, raw) →
    AfterGcdReady roots buffers size →
    Roots.run calls division BmTerminal.fieldDictionary kernels roots .Gcd workspace meter =
      .ok ((outcome roots buffers size).1, (outcome roots buffers size).2,
        rebuild workspace roots { buffers with gcd, work, raw }, id, paidMeter) := by
  intro buffers gcdCall admitted
  have made := RootSetup.factor_work_refines roots.degree workspace.polynomials workspace.square_table
    workspace.raw workspace.basis polyRoom tableRoom
  change FactorWork.new roots.degree workspace.polynomials workspace.square_table workspace.raw workspace.basis =
    .ok (buffers, RootSetup.restoreWork roots.degree.val workspace.polynomials workspace.square_table) at made
  have traceLen : buffers.trace.length = roots.degree.val := by
    unfold buffers RootSetup.workRegions
    dsimp only
    rw [RebuiltLfsr.prefix_length, Nat.min_eq_left]
    rw [BmEntry.tail_length]
    omega
  have tracePrefix := RebuiltLfsr.shared_prefix_normal buffers.trace roots.trace_len (by omega)
  have leaf : bulksketch.types.Stage.Insts.CoreCmpPartialEqStage.eq .Gcd .Leaf = .ok false := by
    simp [bulksketch.types.Stage.Insts.CoreCmpPartialEqStage.eq, bulksketch.types.Stage.read_discriminant]
  have prepare : bulksketch.types.Stage.Insts.CoreCmpPartialEqStage.eq .Gcd .AffinePreparation = .ok false := by
    simp [bulksketch.types.Stage.Insts.CoreCmpPartialEqStage.eq, bulksketch.types.Stage.read_discriminant]
  have enumerate : bulksketch.types.Stage.Insts.CoreCmpPartialEqStage.eq .Gcd .AffineEnumeration = .ok false := by
    simp [bulksketch.types.Stage.Insts.CoreCmpPartialEqStage.eq, bulksketch.types.Stage.read_discriminant]
  obtain ⟨resultDegree, subtracted, subValue, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := size) (y := 1#usize) (by change 1 ≤ size.val; exact admitted.1))
  have degreeValue : resultDegree.val = size.val - 1 := subValue
  have degreeWord : resultDegree = degree size := by
    apply Usize.bv_eq_imp_eq
    change resultDegree.bv = BitVec.ofNat System.Platform.numBits (size.val - 1)
    rw [← degreeValue, Usize.BitVec_ofNat_val]
  have bits : BmTerminal.fieldDictionary.BITS = .ok 64#u32 := by
    change Result.ok bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS = _
    rw [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS]
  simp only [Roots.run, bind_ok, Bool.false_eq_true, ite_false, leaf, prepare, enumerate, made]
  dsimp! only
  simp only [charge, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  dsimp! only
  simp only [bind_ok, Slice.index_SliceIndexRangeToUsizeSliceInst, tracePrefix, gcdCall]
  dsimp! only
  simp only [subtracted, bind_ok]
  by_cases proper : Proper roots size
  · have positive : 0#usize < resultDegree := by
      rw [UScalar.lt_equiv, degreeValue]
      exact proper.1
    have smaller : resultDegree < roots.degree := by rw [UScalar.lt_equiv, degreeValue]; exact proper.2
    simp only [positive, smaller, ite_true]
    simp only [outcome, show 0 < size.val - 1 ∧ size.val - 1 < roots.degree.val from proper,
      ite_true, degreeWord, rebuild]
    all_goals rfl
  · have readyAffine := admitted.2.1 proper
    have readyDirection := admitted.2.2 proper
    have notProper : ¬ (0 < size.val - 1 ∧ size.val - 1 < roots.degree.val) := proper
    by_cases positive : 0#usize < resultDegree <;> (
      first
      | have larger : ¬resultDegree < roots.degree := by
          intro small
          apply proper
          rw [UScalar.lt_equiv, degreeValue] at positive small
          exact ⟨positive, small⟩
        simp only [positive, larger, ite_true, ite_false]
      | simp only [positive, ite_false])
    all_goals
      cases affine : roots.affine
      · obtain ⟨direction, plus, value⟩ := RawMulTable.normal_of_spec _ _
          (U32.add_spec (x := roots.direction) (y := 1#u32) (by exact readyDirection affine))
        have exactDirection : direction = nextDirection roots := by
          apply U32.bv_eq_imp_eq
          change direction.bv = BitVec.ofNat 32 (roots.direction.val + 1)
          change direction.val = roots.direction.val + 1 at value
          rw [← value, U32.BitVec_ofNat_val]
        simp only [affine, Bool.false_eq_true, ite_false, plus, bind_ok, bits, exactDirection,
          outcome, notProper, degreeWord, rebuild]
        by_cases stop : nextDirection roots = 64#u32 <;>
          simp only [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS, stop, ite_true, ite_false] <;> rfl
      · obtain ⟨rankPositive, basisRoom⟩ := readyAffine affine
        obtain ⟨prior, minus, value, _⟩ := RawMulTable.normal_of_spec _ _
          (Usize.sub_spec (x := roots.affine_rank) (y := 1#usize) (by change 1 ≤ roots.affine_rank.val; omega))
        have exactPrior : prior = previousRank roots := by
          apply Usize.bv_eq_imp_eq
          change prior.bv = BitVec.ofNat System.Platform.numBits (roots.affine_rank.val - 1)
          change prior.val = roots.affine_rank.val - 1 at value
          rw [← value, Usize.BitVec_ofNat_val]
        by_cases one : size = 1#usize
        · obtain ⟨present, capacity⟩ := basisRoom one
          cases found : buffers.basis.directions with
          | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at present
          | some basis =>
            have fits : prior.val < (64#usize : Usize).val := by
              change prior.val < 64
              change prior.val = roots.affine_rank.val - 1 at value
              omega
            have active : prior.val < basis.val.length := by rwa [Array.length_eq]
            obtain ⟨word, read, exactWord⟩ := RawMulTable.normal_of_spec _ _
              (Array.index_usize_spec basis prior active)
            have wordEq : word = basisAt buffers (previousRank roots).val := by
              simp only [basisAt, found, ← exactPrior, exactWord]
              exact List.Inhabited_getElem_eq_getElem! _ _ active
            have oneNotProper : ¬ (0 < (1#usize : Usize).val - 1 ∧ (1#usize : Usize).val - 1 < roots.degree.val) := by
              change ¬ (0 < 1 - 1 ∧ _)
              omega
            simp only [affine, ite_true, minus, bind_ok, one, found, RootRunRuntime.optionAsRef,
              core.option.Option.expect, Result.ofOption, lift, outcome, oneNotProper, ite_false, degreeWord, rebuild]
            rw [read, bind_ok, wordEq, exactPrior]
            rfl
        · simp only [affine, ite_true, minus, bind_ok, one, ite_false, outcome, notProper, degreeWord, exactPrior, rebuild]
          rfl

theorem run_gcd_charge_failure (calls : RootRunRuntime.OtherCallees) (division : DenseDivisionRuntime.DivRem)
    {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) (roots : Roots)
    (workspace : RowWorkspace) (meter failedMeter : WorkMeter) (error : DecodeError)
    (polyRoom : 3 * roots.degree.val + 2 ≤ workspace.polynomials.length)
    (tableRoom : RootSetup.tableCount roots.degree.val ≤ workspace.square_table.length)
    (charge : bulksketch.decode.roots.charge meter (.Gcd roots.degree) = .ok (.Err error, failedMeter)) :
    let buffers := RootSetup.workRegions roots.degree.val workspace.polynomials workspace.square_table workspace.raw workspace.basis
    Roots.run calls division BmTerminal.fieldDictionary kernels roots .Gcd workspace meter =
      .ok (.Err error, roots, rebuild workspace roots buffers, id, failedMeter) := by
  intro buffers
  have made := RootSetup.factor_work_refines roots.degree workspace.polynomials workspace.square_table
    workspace.raw workspace.basis polyRoom tableRoom
  change FactorWork.new roots.degree workspace.polynomials workspace.square_table workspace.raw workspace.basis =
    .ok (buffers, RootSetup.restoreWork roots.degree.val workspace.polynomials workspace.square_table) at made
  have leaf : bulksketch.types.Stage.Insts.CoreCmpPartialEqStage.eq .Gcd .Leaf = .ok false := by
    simp [bulksketch.types.Stage.Insts.CoreCmpPartialEqStage.eq, bulksketch.types.Stage.read_discriminant]
  have prepare : bulksketch.types.Stage.Insts.CoreCmpPartialEqStage.eq .Gcd .AffinePreparation = .ok false := by
    simp [bulksketch.types.Stage.Insts.CoreCmpPartialEqStage.eq, bulksketch.types.Stage.read_discriminant]
  have enumerate : bulksketch.types.Stage.Insts.CoreCmpPartialEqStage.eq .Gcd .AffineEnumeration = .ok false := by
    simp [bulksketch.types.Stage.Insts.CoreCmpPartialEqStage.eq, bulksketch.types.Stage.read_discriminant]
  simp only [Roots.run, bind_ok, Bool.false_eq_true, ite_false, leaf, prepare, enumerate, made]
  dsimp! only
  simp only [charge, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  dsimp! only
  simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
    bind_ok, rebuild]
  simp only [Bind.bind, bind_ok]
  rfl

/-- Exact native root GCD stage and the canonical GF64 polynomial
produced by the original Dense callee. The state retry constraints
are explicit so later traversal can discharge them from its cache. -/
theorem run_gcd_composed (calls : RootRunRuntime.OtherCallees) (division : DenseDivisionRuntime.DivRem)
    {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) (roots : Roots)
    (workspace : RowWorkspace) (meter paidMeter : WorkMeter)
    (polyRoom : 3 * roots.degree.val + 2 ≤ workspace.polynomials.length)
    (tableRoom : RootSetup.tableCount roots.degree.val ≤ workspace.square_table.length)
    (traceRoom : roots.trace_len.val ≤ roots.degree.val)
    (charge : bulksketch.decode.roots.charge meter (.Gcd roots.degree) = .ok (.Ok (), paidMeter))
    (law : DenseGcd.DivisionLaw division kernels) (meaning : DenseGcd.DivisionMeaning division kernels)
    (inverse : BmTerminal.NativeInverse kernels) (scale : TimesXMod.ExactScaleXor kernels) :
    let buffers := RootSetup.workRegions roots.degree.val workspace.polynomials workspace.square_table workspace.raw workspace.basis
    let trace := prefixSlice buffers.trace roots.trace_len.val
    let limit := max buffers.modulus.length trace.length
    DenseGcd.Normal buffers.modulus → DenseGcd.Normal trace →
    (SliceKernels.slicePolynomial buffers.modulus).Monic →
    limit ≤ buffers.gcd.length → 4 * (limit + 1) ≤ buffers.work.length → 2 * (limit + 1) ≤ buffers.raw.length →
    (∀ size, 0 < size.val → size.val ≤ limit → AfterGcdReady roots buffers size) →
    ∃ (size : Usize) (result work : Slice U64) (raw : Slice RawProduct),
      SliceKernels.slicePolynomial (prefixSlice result size.val) =
        gcd (SliceKernels.slicePolynomial buffers.modulus) (SliceKernels.slicePolynomial trace) ∧
      0 < size.val ∧
      Roots.run calls division BmTerminal.fieldDictionary kernels roots .Gcd workspace meter =
        .ok ((outcome roots buffers size).1, (outcome roots buffers size).2,
          rebuild workspace roots { buffers with gcd := result, work, raw }, id, paidMeter) := by
  intro buffers trace limit modulusNormal traceNormal monic gcdRoom workRoom rawRoom stageRoom
  obtain ⟨size, result, work, raw, native, _, upper, exactGcd⟩ :=
    DenseGcd.monic_gcd_meaning division kernels buffers.modulus trace buffers.gcd buffers.work buffers.raw
      law meaning inverse scale modulusNormal traceNormal gcdRoom workRoom rawRoom
  have positive : 0 < size.val := by
    by_contra empty
    have sizeZero : size.val = 0 := by omega
    have polynomialZero : SliceKernels.slicePolynomial (prefixSlice result size.val) = 0 := by
      rw [sizeZero]
      simp only [SliceKernels.slicePolynomial, RebuiltLfsr.prefix_length, Nat.zero_min,
        Finset.range_zero, Finset.sum_empty]
    have zeroGcd := exactGcd.symm.trans polynomialZero
    exact monic.ne_zero ((gcd_eq_zero_iff _ _).mp zeroGcd).1
  refine ⟨size, result, work, raw, exactGcd, positive, ?_⟩
  exact run_gcd_paid calls division kernels roots workspace meter paidMeter polyRoom tableRoom traceRoom charge
    size result work raw native (stageRoom size positive upper)


end BulksketchBridge.RootRun
