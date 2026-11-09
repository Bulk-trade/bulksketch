import Arithmetic.RootAffinePreparationGenerated
import BulksketchBridge.RootAffinePreparationPrice
import BulksketchBridge.ClosedLeafWindows
import BulksketchBridge.BmEntry
import BulksketchBridge.RootSetupSpec

namespace BulksketchBridge.RootAffinePreparation

open Aeneas Aeneas.Std DenseCoefficient RebuiltLfsr BmEntry
open bulksketch.decode.roots bulksketch.decode.scratch bulksketch.backend.contract bulksketch.types
open core.result.Result.Insts
open RootRun (affinePreparationCost affine_preparation_cost_refines roots_charge_returns)

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

abbrev Calls := RootAffinePreparationRuntime.Callees
abbrev dictionary := RootSetup.gf64Dictionary
abbrev Frame := core.result.Result (core.result.Result Stage DecodeFailure) DecodeError ×
  Roots × RowWorkspace × (RowWorkspace → RowWorkspace) × WorkMeter

def multipleInput (calls : Calls) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) :=
  calls.multiple dictionary kernels
    (prefixSlice workspace.polynomials (roots.degree.val + 1))
    (prefixSlice workspace.square_table (RootSetup.tableCount roots.degree.val)) workspace.factors
    (prefixSlice workspace.bm (roots.degree.val + 1)) (tail workspace.bm (roots.degree.val + 1)) workspace.raw

def mapInput {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (size : Usize) (coefficients : Slice U64) :=
  bulksketch.decode.affine.solve_map dictionary kernels
    (prefixSlice coefficients size.val) (Array.repeat 64#usize 0#u64)

/-- Bounds for the paid stage, stated on the actual buffers returned by the
    affine multiple and solve-map calls. -/
def Ready (calls : Calls) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) : Prop :=
  roots.degree.val < workspace.polynomials.length ∧
  roots.degree.val + 1 ≤ workspace.bm.length ∧
  RootSetup.tableCount roots.degree.val ≤ workspace.square_table.length ∧
  ∃ size factors coefficients work raw,
    multipleInput calls kernels roots workspace = .ok (size, factors, coefficients, work, raw) ∧
    1 < coefficients.length ∧ (coefficients[(1 : Nat)]! ≠ 0#u64 →
      size.val ≤ coefficients.length ∧ 0 < size.val ∧
      ∃ solution directions,
        mapInput kernels size coefficients = .ok (solution, directions) ∧
        match solution with
        | none => True
        | some (_, rank) => rank.val ≤ 64 ∧ roots.stride.val * roots.stride.val ≤ factors.length)

def insufficientPoints (degree rank : Usize) : Bool :=
  decide (rank.val < 64 ∧ 2 ^ rank.val < degree.val)

def expected (calls : Calls) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter : WorkMeter) : Result Frame := do
  let (charged, paid) := StageCharge.chargeResult meter (affinePreparationCost roots.degree)
  match charged with
  | .Err error => .ok (.Err error, roots, workspace, id, paid)
  | .Ok () =>
    let (size, factors, coefficients, work, raw) ← multipleInput calls kernels roots workspace
    let written := { workspace with bm := splitBack workspace.bm (roots.degree.val + 1) (coefficients, work), factors, raw }
    if coefficients[(1 : Nat)]! = 0#u64 then
      .ok (.Ok (.Err .NotSplit), roots, written, id, paid)
    else do
      let (solution, directions) ← mapInput kernels size coefficients
      let based := { written with basis := { workspace.basis with directions := some directions } }
      match solution with
      | none => .ok (.Ok (.Err .NotSplit), roots, based, id, paid)
      | some (base, rank) =>
        if size.val - 1 ≤ rank.val then
          .ok (.Ok (.Err .NotSplit), roots, based, id, paid)
        else if insufficientPoints roots.degree rank then
          .ok (.Ok (.Err .NotSplit), roots, based, id, paid)
        else do
          let enumerate ← bulksketch.decode.affine.enumerate_preferred roots.degree rank
          let readyRoots := { roots with affine_ready := true, affine_base := base, affine_rank := rank }
          let readyWork := { based with basis := { based.basis with len := UScalar.cast .U32 rank } }
          if enumerate then
            .ok (.Ok (.Ok .AffineEnumeration), readyRoots, readyWork, id, paid)
          else do
            let offset := roots.stride.val * roots.stride.val
            let updated ← bulksketch.decode.affine.subspaces dictionary kernels
              (prefixSlice directions.to_slice rank.val) (tail factors offset)
            .ok (.Ok (.Ok .AffineSplit), readyRoots, { readyWork with factors := factors.setSlice! offset updated.val }, id, paid)

def ActualAffinePreparation : Prop :=
  ∀ (calls : Calls) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter : WorkMeter),
    (∀ paid, charge meter (.AffinePreparation roots.degree) = .ok (.Ok (), paid) →
      Ready calls kernels roots workspace) →
    Roots.prepare_affine calls dictionary kernels roots workspace meter = expected calls kernels roots workspace meter

private theorem read_word (words : Slice U64) (index : Usize) (bounded : index.val < words.length) :
    Slice.index_usize words index = Result.ok words[index.val]! := by
  obtain ⟨word, normal, exactValue⟩ := RawMulTable.normal_of_spec _ _
    (Slice.index_usize_spec words index bounded)
  rw [normal, exactValue, Slice.getElem!_Nat_eq]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! _ _ bounded)

private theorem count_guard {K A : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (degree rank : Usize) (rankBound : rank.val ≤ 64) (finish : Bool → Result A) :
    (do
      let points ← core.num.U64.checked_shl 1#u64 (UScalar.cast .U32 rank)
      let tooFew ← core.option.Option.is_some_and
        (Roots.prepare_affine.closure.Insts.CoreOpsFunctionFnOnceTupleU64Bool dictionary kernels)
        points degree
      finish tooFew) = finish (insufficientPoints degree rank) := by
  have rankValue : (UScalar.cast .U32 rank).val = rank.val := by
    rw [UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (by change rank.val < 2 ^ 32; omega)
  have degreeValue : (UScalar.cast .U64 degree).val = degree.val := by
    rw [UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    exact lt_of_lt_of_le degree.hBounds (Nat.pow_le_pow_right (by decide) System.Platform.numBits_le)
  by_cases small : rank.val < 64
  · have pointsValue : (⟨(1#u64).bv <<< rank.val⟩ : U64).val = 2 ^ rank.val := by
      change ((1#u64).bv <<< rank.val).toNat = _
      rw [BitVec.toNat_shiftLeft, show (1#u64).bv.toNat = 1 from rfl, Nat.shiftLeft_eq, Nat.one_mul]
      change 2 ^ rank.val % 2 ^ 64 = _
      rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) small)]
    simp only [core.num.U64.checked_shl, rankValue, small, ite_true, bind_ok,
      core.option.Option.is_some_and, Roots.prepare_affine.closure.Insts.CoreOpsFunctionFnOnceTupleU64Bool.call_once,
      lift, insufficientPoints, UScalar.lt_equiv, pointsValue, degreeValue, true_and]
  · simp only [core.num.U64.checked_shl, rankValue, small, ite_false, bind_ok,
      core.option.Option.is_some_and, insufficientPoints, false_and, decide_false]

private theorem factor_suffix (words : Slice U64) (offset : Usize) (bounded : offset.val ≤ words.length) :
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut ⟨offset⟩ words =
      .ok (tail words offset.val, fun updated => words.setSlice! offset.val updated.val) := by
  obtain ⟨⟨suffix, back⟩, normal, suffixValue, _, backValue⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut.step_spec ⟨offset⟩ words bounded)
  have suffixEq : suffix = tail words offset.val := by
    apply Slice.ext
    simpa only [tail, Slice.from_val] using suffixValue
  have backEq : back = (fun updated => words.setSlice! offset.val updated.val) := by
    funext replacement
    apply Slice.ext
    simpa only [Slice.setSlice!_val] using backValue replacement
  rw [normal, suffixEq, backEq]

theorem prepare_affine_refines : ActualAffinePreparation := by
  intro calls K kernels roots workspace meter ready
  have charged := roots_charge_returns meter (.AffinePreparation roots.degree)
    (affinePreparationCost roots.degree) (affine_preparation_cost_refines roots.degree)
  rcases paidEq : StageCharge.chargeResult meter (affinePreparationCost roots.degree) with ⟨reply, paid⟩
  rw [paidEq] at charged
  cases reply with
  | Err error =>
    simp only [expected, paidEq, Roots.prepare_affine, charged, bind_ok, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from, Bind.bind]
    dsimp! only
    simp only [bind_ok]
    rfl
  | Ok successful =>
    cases successful
    obtain ⟨polyRoom, bmRoom, tableRoom, size, factors, coefficients, work, raw, multiple, coeffRoom, mapReady⟩ :=
      ready paid charged
    have bmMax : workspace.bm.length ≤ Usize.max := workspace.bm.length_ineq
    have tableMax : workspace.square_table.length ≤ Usize.max := workspace.square_table.length_ineq
    obtain ⟨width, addOk, widthValue⟩ := RawMulTable.normal_of_spec _ _
      (Usize.add_spec (x := roots.degree) (y := 1#usize) (by
        change roots.degree.val + 1 ≤ Usize.max
        omega))
    change width.val = roots.degree.val + 1 at widthValue
    obtain ⟨half, halfOk, halfValue⟩ := RawMulTable.normal_of_spec _ _
      (Usize.div_spec roots.degree (y := 2#usize) (by simp))
    change half.val = roots.degree.val / 2 at halfValue
    obtain ⟨count, mulOk, countValue⟩ := RawMulTable.normal_of_spec _ _
      (Usize.mul_spec (x := roots.degree) (y := half) (by
        rw [halfValue, ← RootSetup.tableCount]
        omega))
    change count.val = roots.degree.val * half.val at countValue
    rw [halfValue, ← RootSetup.tableCount] at countValue
    have split := split_refines workspace.bm width (by omega)
    have modulus := ClosedLeaf.inclusive_prefix_normal workspace.polynomials roots.degree polyRoom
    have table := shared_prefix_normal workspace.square_table count (by omega)
    have read := read_word coefficients 1#usize coeffRoom
    rw [show (1#usize).val = 1 from rfl] at read
    simp only [expected, paidEq, Roots.prepare_affine, charged, bind_ok, CoreOpsTry.branch]
    dsimp! only
    simp only [bind_ok, addOk, split, core.slice.index.Slice.index, modulus, halfOk, mulOk, table,
      countValue, widthValue]
    dsimp! only
    unfold multipleInput at multiple ⊢
    simp only [multiple, bind_ok]
    dsimp! only
    by_cases zero : coefficients[(1 : Nat)]! = 0#u64
    · simp only [read, bind_ok, zero, ite_true]
      rfl
    · obtain ⟨sizeRoom, sizePositive, solution, directions, solved, ranked⟩ := mapReady zero
      have coeffPrefix := shared_prefix_normal coefficients size sizeRoom
      simp only [read, bind_ok, zero, ite_false, RootAffinePreparationRuntime.insertBasis]
      dsimp! only
      unfold mapInput at solved ⊢
      simp only [bind_ok, coeffPrefix, solved]
      dsimp! only
      cases solution with
      | none =>
        rfl
      | some solution =>
        obtain ⟨base, rank⟩ := solution
        obtain ⟨rankBound, factorsRoom⟩ := ranked
        obtain ⟨last, subOk, lastValue, _⟩ := RawMulTable.normal_of_spec _ _
          (Usize.sub_spec (x := size) (y := 1#usize) (by exact sizePositive))
        change last.val = size.val - 1 at lastValue
        simp only [bind_ok, subOk, UScalar.le_equiv, lastValue]
        by_cases rankLarge : size.val - 1 ≤ rank.val
        · simp only [rankLarge, ite_true]
          rfl
        · simp only [rankLarge, ite_false, lift, bind_ok]
          have factorsMax : factors.length ≤ Usize.max := factors.length_ineq
          obtain ⟨offset, offsetOk, offsetValue⟩ := RawMulTable.normal_of_spec _ _
            (Usize.mul_spec (x := roots.stride) (y := roots.stride) (factorsRoom.trans factorsMax))
          have suffix := factor_suffix factors offset (by omega)
          have basisPrefix :
              core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U64))
                directions { «end» := rank } = .ok (prefixSlice directions.to_slice rank.val) := by
            rw [Array.index_SliceIndexRangeToUsizeSlice, shared_prefix_normal]
            simpa only [Array.length_to_slice, show (64#usize).val = 64 by decide] using rankBound
          simp only [count_guard kernels roots.degree rank rankBound, bind_ok, offsetOk,
            Slice.index_mut_SliceIndexRangeFromUsizeSliceInst, suffix, basisPrefix, offsetValue]
          rfl

end BulksketchBridge.RootAffinePreparation
