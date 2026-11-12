import BulksketchBridge.BmEntry
import BulksketchBridge.AffineGrayFill
import BulksketchBridge.AffineCandidateScan
import BulksketchBridge.SlicePolynomial
import BulksketchBridge.ClosedLeafAdvance

namespace BulksketchBridge.AffineEnumerate

open Aeneas Aeneas.Std DenseCoefficient RebuiltLfsr SliceKernels Algebra.Gf64 Polynomial
open bulksketch.backend.contract bulksketch.decode.affine bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

abbrev BatchIterator := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)

def batchAt (start stop batch : Usize) : BatchIterator := ⟨⟨start, stop⟩, batch⟩

abbrev nextBatch := core.iter.adapters.step_by.IteratorStepBy.next
  (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)

def HornerLaw {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) : Prop :=
  ∀ (polynomial points values : Slice U64), points.length = values.length →
    ∃ evaluated,
      kernels.horner_many polynomial points values = .ok evaluated ∧
      evaluated.length = values.length ∧
      ∀ i < points.length,
        toField evaluated[i]!.bv = (slicePolynomial polynomial).eval (toField points[i]!.bv)

theorem next_batch (start stop batch : Usize) (nonzero : 0 < batch.val) (active : start.val < stop.val) :
    ∃ cursor,
      nextBatch (batchAt start stop batch) = .ok (some start, batchAt cursor stop batch) ∧
      cursor.val = min (start.val + batch.val) stop.val := by
  obtain ⟨⟨option, ⟨⟨cursor, limit⟩, width⟩⟩, normal, post⟩ := RawMulTable.normal_of_spec _ _
    (core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec (batchAt start stop batch) nonzero)
  change (if start.val < stop.val then option = some start ∧ cursor.val = min (start.val + batch.val) stop.val
    else option = none ∧ cursor = start) ∧ limit = stop ∧ width = batch at post
  rw [ite_eq_left active] at post
  obtain ⟨⟨rfl, index⟩, rfl, rfl⟩ := post
  exact ⟨cursor, normal, index⟩

theorem batches_done (start stop batch : Usize) (nonzero : 0 < batch.val) (ended : stop.val ≤ start.val) :
    nextBatch (batchAt start stop batch) = .ok (none, batchAt start stop batch) := by
  obtain ⟨⟨option, ⟨⟨cursor, limit⟩, width⟩⟩, normal, post⟩ := RawMulTable.normal_of_spec _ _
    (core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec (batchAt start stop batch) nonzero)
  change (if start.val < stop.val then option = some start ∧ cursor.val = min (start.val + batch.val) stop.val
    else option = none ∧ cursor = start) ∧ limit = stop ∧ width = batch at post
  rw [ite_eq_right (Nat.not_lt.mpr ended)] at post
  obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := post
  exact normal

private theorem restore_active_prefix (original updated : Slice U64) (width : Nat)
    (fits : width ≤ original.length) (same : updated.length = width) :
    prefixSlice (restorePrefix original updated) width = updated := by
  apply Slice.ext
  have bound : updated.val.length ≤ original.val.length := same.trans_le fits
  simp only [prefixSlice, restorePrefix, Slice.from_val, List.setSlice!, Nat.sub_zero, Nat.zero_add,
    List.take_zero, List.nil_append, Nat.min_eq_left bound, List.take_length]
  rw [← same, List.take_left]

theorem batch_step {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (horner : HornerLaw kernels) (rejoin : Slice U64 × Slice U64 → Slice U64)
    (polynomial basis roots points values : Slice U64) (degree batch start stop found : Usize) (x : U64)
    (positive : 0 < batch.val) (active : start.val < stop.val)
    (pointsRoom : batch.val ≤ points.length) (valuesRoom : batch.val ≤ values.length)
    (rootsRoom : degree.val ≤ roots.length) (foundRoom : found.val ≤ degree.val)
    (cosetRoom : stop.val ≤ 2 ^ basis.length) :
    let width := min batch.val (stop.val - start.val)
    let filled := grayFill basis start.val (prefixSlice points width) 0 x width
    let points' := restorePrefix points filled.2
    ∃ cursor evaluated failure roots' found',
      cursor.val = start.val + width ∧ evaluated.length = width ∧
      kernels.horner_many polynomial filled.2 (prefixSlice values width) = .ok evaluated ∧
      (∀ i < width, toField evaluated[i]!.bv = (slicePolynomial polynomial).eval (toField filled.2[i]!.bv)) ∧
      scan degree.val (List.zip filled.2.val evaluated.val) roots found.val = (failure, roots', found'.val) ∧
      roots'.length = roots.length ∧ found'.val ≤ degree.val ∧
      let values' := restorePrefix values evaluated
      enumerate_loop0.body kernels rejoin polynomial basis degree batch stop (batchAt start stop batch)
        roots points values x found =
        .ok (match failure with
        | none => .cont (batchAt cursor stop batch, roots', points', values', filled.1, found')
        | some reason => .done (.Err reason, roots', rejoin (points', values'))) := by
  dsimp only
  obtain ⟨cursor, stepped, nextValue⟩ := next_batch start stop batch positive active
  obtain ⟨remaining, subOk, remainingValue, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := stop) (y := start) (by omega))
  let len := core.cmp.impls.OrdUsize.min batch remaining
  have lenValue : len.val = min batch.val (stop.val - start.val) := by
    simp only [len, core.cmp.impls.OrdUsize.min_val, remainingValue]
  have nextExact : cursor.val = start.val + len.val := by
    rw [nextValue, lenValue]
    omega
  have pointCut : len.val ≤ points.length := by omega
  have valueCut : len.val ≤ values.length := by omega
  have pointWidth : (prefixSlice points len.val).length = len.val := by rw [prefix_length, Nat.min_eq_left pointCut]
  have valueWidth : (prefixSlice values len.val).length = len.val := by rw [prefix_length, Nat.min_eq_left valueCut]
  let filled := grayFill basis start.val (prefixSlice points len.val) 0 x len.val
  have filledWidth : filled.2.length = len.val :=
    (gray_fill_words basis (prefixSlice points len.val) start.val 0 x len.val (by omega)).2.1.trans pointWidth
  obtain ⟨evaluated, hornerNormal, evaluatedWidth, evaluations⟩ :=
    horner polynomial filled.2 (prefixSlice values len.val) (filledWidth.trans valueWidth.symm)
  rw [valueWidth] at evaluatedWidth
  obtain ⟨failure, written, found', scanned, scanNormal, rootsWidth, countBound⟩ :=
    candidate_scan_refines filled.2 evaluated roots degree found 0 (filledWidth.trans evaluatedWidth.symm)
      rootsRoom foundRoom
  simp only [List.drop_zero] at scanned
  rw [← lenValue]
  refine ⟨cursor, evaluated, failure, written, found', nextExact, evaluatedWidth, hornerNormal, ?_, scanned,
    rootsWidth, countBound, ?_⟩
  · intro index inside
    exact evaluations index (by omega)
  simp only [enumerate_loop0.body, stepped, bind_ok, lift]
  dsimp! only
  simp only [subOk, bind_ok]
  change fillPointsPrefix basis points start len x (fun nextPoint nextPoints => do
    let shared ← core.slice.index.SliceIndexRangeToUsizeSlice.index ⟨len⟩ nextPoints
    let (output, restore) ← core.slice.index.SliceIndexRangeToUsizeSlice.index_mut ⟨len⟩ values
    let evaluated ← kernels.horner_many polynomial shared output
    let iter ← core.slice.Slice.iter shared
    let nextValues := restore evaluated
    let read ← core.slice.index.SliceIndexRangeToUsizeSlice.index ⟨len⟩ nextValues
    let paired ← Aeneas.Std.core.iter.traits.iterator.Iterator.zip.trait_default
      (core.iter.traits.iterator.IteratorSliceIter U64)
      (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U64) iter read
    let (reason, written, found', more) ← enumerate_loop0_loop1 paired roots degree found
    if more then .ok (ControlFlow.cont (batchAt cursor stop batch, written, nextPoints, nextValues, nextPoint, found'))
    else .ok (ControlFlow.done (core.result.Result.Err reason, written, rejoin (nextPoints, nextValues)))) = _
  have stopFits : stop.val ≤ Usize.max := by scalar_tac
  rw [gray_fill_prefix_refines _ _ _ _ _ _ pointCut (by omega) (by omega)]
  dsimp only
  have sharedPoints := shared_prefix_normal (restorePrefix points filled.2) len (by rw [restore_length]; exact pointCut)
  have sharedValues := shared_prefix_normal (restorePrefix values evaluated) len (by rw [restore_length]; exact valueCut)
  rw [restore_active_prefix points filled.2 len.val pointCut filledWidth] at sharedPoints
  rw [restore_active_prefix values evaluated len.val valueCut evaluatedWidth] at sharedValues
  rw [sharedPoints]
  simp only [prefix_normal values len valueCut, bind_ok]
  dsimp! only
  rw [hornerNormal]
  simp only [bind_ok, core.slice.Slice.iter]
  rw [sharedValues]
  have paired :
      Aeneas.Std.core.iter.traits.iterator.Iterator.zip.trait_default
        (core.iter.traits.iterator.IteratorSliceIter U64)
        (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U64) ⟨filled.2, 0⟩ evaluated =
        .ok (zipAt filled.2 evaluated 0) := by
    simp [Aeneas.Std.core.iter.traits.iterator.Iterator.zip.trait_default,
      Aeneas.Std.core.iter.traits.iterator.Iterator.zip.default,
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, zipAt]
  simp only [bind_ok]
  rw [paired]
  simp only [bind_ok]
  rw [scanNormal]
  simp only [bind_ok]
  dsimp! only
  cases failure <;> rfl

theorem batch_done {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (rejoin : Slice U64 × Slice U64 → Slice U64) (polynomial basis roots points values : Slice U64)
    (degree batch start stop found : Usize) (x : U64)
    (positive : 0 < batch.val) (ended : stop.val ≤ start.val) :
    enumerate_loop0.body kernels rejoin polynomial basis degree batch stop (batchAt start stop batch)
        roots points values x found =
      .ok (.done (if found.val = degree.val then .Ok found else .Err .NotSplit,
        roots, rejoin (points, values))) := by
  simp only [enumerate_loop0.body, batches_done start stop batch positive ended, bind_ok]
  dsimp! only
  by_cases same : found = degree
  · subst found
    simp
  · have different : found.val ≠ degree.val := fun equal => same (UScalar.eq_of_val_eq equal)
    simp [same, different]

abbrev BatchResult := core.result.Result Usize DecodeFailure × Slice U64 × Slice U64

/-- Candidate count decreases by the true width of each batch, including
the final tail. The mathematical model threads the exact scratch frame. -/
def enumerateBatches {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (rejoin : Slice U64 × Slice U64 → Slice U64) (polynomial basis : Slice U64)
    (degree batch stop start : Nat) (roots points values : Slice U64)
    (x : U64) (found : Nat) : Result BatchResult :=
  if _active : start < stop ∧ 0 < batch then do
    let width := min batch (stop - start)
    let filled := grayFill basis start (prefixSlice points width) 0 x width
    let evaluated ← kernels.horner_many polynomial filled.2 (prefixSlice values width)
    let (failure, written, nextCount) := scan degree (List.zip filled.2.val evaluated.val) roots found
    let nextPoints := restorePrefix points filled.2
    let nextValues := restorePrefix values evaluated
    match failure with
    | some reason => .ok (.Err reason, written, rejoin (nextPoints, nextValues))
    | none =>
      enumerateBatches kernels rejoin polynomial basis degree batch stop (start + width)
        written nextPoints nextValues filled.1 nextCount
  else
    .ok (if found = degree then .Ok (ClosedLeafAdvance.usizeWord found) else .Err .NotSplit,
      roots, rejoin (points, values))
termination_by stop - start
decreasing_by
  have positive : 0 < width := Nat.lt_min.mpr ⟨_active.2, by omega⟩
  omega

theorem batches_refine {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (horner : HornerLaw kernels) (rejoin : Slice U64 × Slice U64 → Slice U64)
    (polynomial basis roots points values : Slice U64) (degree batch start stop found : Usize) (x : U64)
    (positive : 0 < batch.val) (pointsRoom : batch.val ≤ points.length) (valuesRoom : batch.val ≤ values.length)
    (rootsRoom : degree.val ≤ roots.length) (foundRoom : found.val ≤ degree.val)
    (cosetRoom : stop.val ≤ 2 ^ basis.length) :
    enumerate_loop0 kernels rejoin (batchAt start stop batch) polynomial basis roots degree points values
      batch stop x found =
      enumerateBatches kernels rejoin polynomial basis degree.val batch.val stop.val start.val roots points values x found.val := by
  suffices ∀ (fuel : Nat) (start found : Usize) (roots points values : Slice U64) (x : U64),
      stop.val - start.val = fuel →
      batch.val ≤ points.length → batch.val ≤ values.length →
      degree.val ≤ roots.length → found.val ≤ degree.val →
      enumerate_loop0 kernels rejoin (batchAt start stop batch) polynomial basis roots degree points values
        batch stop x found =
      enumerateBatches kernels rejoin polynomial basis degree.val batch.val stop.val start.val roots points values x found.val
    from this _ start found roots points values x rfl pointsRoom valuesRoom rootsRoom foundRoom
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro start found roots points values x remaining pointsRoom valuesRoom rootsRoom foundRoom
    by_cases active : start.val < stop.val
    · obtain ⟨cursor, evaluated, failure, written, nextCount, advanced, _, normal, _, scanned, rootsWidth,
        countBound, body⟩ := batch_step kernels horner rejoin polynomial basis roots points values degree
          batch start stop found x positive active pointsRoom valuesRoom rootsRoom foundRoom cosetRoom
      let width := min batch.val (stop.val - start.val)
      let filled := grayFill basis start.val (prefixSlice points width) 0 x width
      have activeBatch : start.val < stop.val ∧ 0 < batch.val := ⟨active, positive⟩
      unfold enumerate_loop0 loop
      dsimp only
      rw [body, enumerateBatches, dite_eq_left activeBatch]
      dsimp only
      simp only [normal, bind_ok, scanned]
      dsimp! only
      cases failure with
      | some reason => rfl
      | none =>
        have widthPositive : 0 < width := Nat.lt_min.mpr ⟨positive, by omega⟩
        have decrease : stop.val - cursor.val < fuel := by
          change cursor.val = start.val + width at advanced
          omega
        have step := ih _ decrease cursor nextCount written (restorePrefix points filled.2)
          (restorePrefix values evaluated) filled.1 rfl (by simpa only [restore_length] using pointsRoom)
          (by simpa only [restore_length] using valuesRoom) (by rwa [rootsWidth]) countBound
        simpa only [enumerate_loop0, advanced, width, filled] using step
    · have ended : stop.val ≤ start.val := Nat.le_of_not_gt active
      have finished := batch_done kernels rejoin polynomial basis roots points values degree
        batch start stop found x positive ended
      unfold enumerate_loop0 loop
      dsimp only
      rw [finished, enumerateBatches, dite_eq_right (fun h => active h.1)]
      simp only [bind_ok]
      have foundExact : ClosedLeafAdvance.usizeWord found.val = found := by
        apply UScalar.eq_of_val_eq
        exact ClosedLeafAdvance.word_val _ (by scalar_tac)
      rw [foundExact]


def batchWidth (half : Nat) : Nat := if 8 ≤ half then half / 8 * 8 else half

def ActualNativeEnumerate : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    HornerLaw kernels → ∀ (polynomial : Slice U64) (base : U64) (basis roots work : Slice U64),
    0 < polynomial.length → polynomial.length - 1 ≤ roots.length →
    2 ≤ work.length → basis.length < System.Platform.numBits →
    let half := work.length / 2
    enumerate bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels polynomial base basis roots work =
      enumerateBatches kernels (BmEntry.splitBack work half) polynomial basis (polynomial.length - 1)
        (batchWidth half) (2 ^ basis.length) 0 roots (prefixSlice work half) (BmEntry.tail work half) base 0

theorem native_enumerate_refines : ActualNativeEnumerate := by
  intro K kernels horner polynomial base basis roots work polyPositive rootRoom workRoom rank
  dsimp only
  obtain ⟨degree, degOk, degVal, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := Slice.len polynomial) (y := 1#usize) (by rw [Slice.len_val]; exact polyPositive))
  change degree.val = (Slice.len polynomial).val - 1 at degVal
  rw [Slice.len_val] at degVal
  obtain ⟨half, halfOk, halfVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.div_spec (Slice.len work) (y := 2#usize) (by simp))
  change half.val = (Slice.len work).val / 2 at halfVal
  rw [Slice.len_val] at halfVal
  let points := prefixSlice work half.val
  let values := BmEntry.tail work half.val
  have pointsLen : points.length = half.val := by
    rw [show points = prefixSlice work half.val from rfl, prefix_length, Nat.min_eq_left (by omega)]
  have valuesLen : values.length = work.length - half.val := BmEntry.tail_length ..
  have minimum :
      core.cmp.impls.OrdUsize.min (Slice.len points) (Slice.len values) = half := by
    apply UScalar.eq_of_val_eq
    rw [core.cmp.impls.OrdUsize.min_val, Slice.len_val, Slice.len_val, pointsLen, valuesLen, Nat.min_eq_left]
    omega
  have halfMax : half.val ≤ Usize.max := by scalar_tac
  have ⟨batch, batchOk, batchVal⟩ :
      ∃ batch : Usize,
        (if half ≥ 8#usize then (do let groups ← half / 8#usize; groups * 8#usize) else .ok half) = .ok batch ∧
        batch.val = batchWidth half.val := by
    by_cases large : 8 ≤ half.val
    · have threshold : half ≥ 8#usize := by exact large
      obtain ⟨groups, divided, count⟩ := RawMulTable.normal_of_spec _ _
        (Usize.div_spec half (y := 8#usize) (by simp))
      change groups.val = half.val / 8 at count
      obtain ⟨batch, multiplied, exactWidth⟩ := RawMulTable.normal_of_spec _ _
        (Usize.mul_spec (x := groups) (y := 8#usize) (by
          change groups.val * 8 ≤ Usize.max
          omega))
      refine ⟨batch, ?_, ?_⟩
      · simp only [threshold, ite_true, divided, Bind.bind, bind_ok, multiplied]
      · change batch.val = groups.val * 8 at exactWidth
        rw [exactWidth, count, batchWidth, ite_eq_left large]
    · have small : ¬ half ≥ 8#usize := by exact large
      exact ⟨half, by rw [ite_eq_right small], by rw [batchWidth, ite_eq_right large]⟩
  have batchBounds : 0 < batch.val ∧ batch.val ≤ half.val := by
    rw [batchVal, batchWidth]
    split <;> omega
  have rankValue : (UScalar.cast .U32 (Slice.len basis)).val = basis.length := by
    have width := System.Platform.numBits_le
    rw [UScalar.cast_val_eq, Slice.len_val]
    exact Nat.mod_eq_of_lt (by change basis.length < 2 ^ 32; omega)
  let stop : Usize := ⟨(1#usize).bv <<< basis.length⟩
  have stopVal : stop.val = 2 ^ basis.length := by
    change ((1#usize).bv <<< basis.length).toNat = _
    rw [BitVec.toNat_shiftLeft, show (1#usize).bv.toNat = 1 from rfl, Nat.shiftLeft_eq, Nat.one_mul]
    change 2 ^ basis.length % 2 ^ System.Platform.numBits = _
    rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) rank)]
  have shifted : Aeneas.Std.MutableEnumerate.checkedShift 1#usize (UScalar.cast .U32 (Slice.len basis)) =
      .ok (some stop) := by
    simp only [Aeneas.Std.MutableEnumerate.checkedShift, rankValue, rank, ite_true, stop]
  have split := BmEntry.split_refines work half (by omega)
  have stepped :
      core.iter.traits.iterator.Iterator.step_by.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) ⟨0#usize, stop⟩ batch =
        .ok (batchAt 0#usize stop batch) := by
    simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
      core.iter.traits.iterator.Iterator.step_by.default, Nat.ne_of_gt batchBounds.1, ite_false, batchAt]
  simp only [enumerate, degOk, halfOk, split, bind_ok, lift]
  dsimp! only
  simp only [points, values] at minimum
  rw [minimum]
  simp only [bind_ok, shifted, core.option.Option.expect, Result.ofOption]
  erw [batchOk]
  simp only [bind_ok, stepped]
  have ran := batches_refine kernels horner (BmEntry.splitBack work half.val) polynomial basis roots points values
    degree batch 0#usize stop 0#usize base batchBounds.1 (by omega) (by omega) (by omega) (by simp) (by omega)
  simpa only [degVal, batchVal, stopVal, halfVal, show (0#usize).val = 0 by simp, points, values] using ran


end BulksketchBridge.AffineEnumerate
