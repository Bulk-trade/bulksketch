import BulksketchBridge.BmEvenStepSpec
import BulksketchBridge.BmDiscrepancy
import BulksketchBridge.BmStepControl
import BulksketchBridge.BmRuntimeFrames
import BulksketchBridge.StageCharge

namespace BulksketchBridge.BmEvenStep

open Aeneas Aeneas.Std Aeneas.Std.WP BmDiscrepancy BmStepControl DenseCoefficient
open bulksketch.backend.contract bulksketch.decode.bm bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

abbrev coefficientPrefix (connection : Slice U64) (degree : Usize) : Slice U64 :=
  prefixSlice connection (degree.val + 1)

abbrev window (syndromes : Slice U64) (degree index : Usize) : Slice U64 :=
  ClosedLeaf.region syndromes (index.val + 1 - degree.val) (index.val + 2)

structure PreludeEquations {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (connection syndromes : Slice U64) (degree index first last : Usize) : Prop where
  nextIndex : (index + 1#usize : Result Usize) = .ok last
  firstIndex : (last - degree : Result Usize) = .ok first
  lastVal : last.val = index.val + 1
  firstVal : first.val = index.val + 1 - degree.val
  coefficients : core.slice.index.Slice.index (RebuiltLfsrRuntime.inclusive U64)
    connection ⟨degree⟩ = .ok (coefficientPrefix connection degree)
  moments : core.slice.index.Slice.index (BmLocatorRuntime.inclusiveRange U64)
    syndromes ⟨first, last, false⟩ = .ok (window syndromes degree index)
  paidLoop : locator_loop0_loop1 fieldDictionary kernels
    (sourceZip connection syndromes degree.val index.val) 0#u64 0#u64 =
    .ok ((rawDelta connection syndromes degree index).lo, (rawDelta connection syndromes degree index).hi)
  firstLoop : locator_loop0_loop6 fieldDictionary kernels
    (sourceZip connection syndromes degree.val index.val) 0#u64 0#u64 =
    .ok ((rawDelta connection syndromes degree index).lo, (rawDelta connection syndromes degree index).hi)
  reduced : kernels.ArithmeticInst.reduce (rawDelta connection syndromes degree index) =
    .ok (deltaWord connection syndromes degree index)

/-- Both exact read-only loop calls start from the same verified source windows. -/
theorem prelude_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (raw : RawArithmetic kernels) (reduce : ReduceArithmetic kernels)
    (connection syndromes : Slice U64) (degree index : Usize)
    (bounds : PreludeBounds connection syndromes degree index) :
    ∃ first last, PreludeEquations kernels connection syndromes degree index first last := by
  have sizeBound : syndromes.length ≤ Usize.max := syndromes.length_ineq
  have syndromeBound := bounds.syndromes
  have lower := bounds.lower
  obtain ⟨last, added, lastVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := index) (y := 1#usize) (by change index.val + 1 ≤ Usize.max; omega))
  change last.val = index.val + 1 at lastVal
  obtain ⟨first, subtracted, firstVal, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := last) (y := degree) (by omega))
  rw [lastVal] at firstVal
  let state := sourceZip connection syndromes degree.val index.val
  let initial : Raw := ⟨0#u64, 0#u64⟩
  obtain ⟨paid, uncharged⟩ := raw_refines kernels raw state.fst.slice state.snd.iter.slice 0 initial
  let product := rawDelta connection syndromes degree index
  obtain ⟨output, normal, bits, _⟩ := Gf64Reduce.reduce_refines product
  have exactOutput : output = deltaWord connection syndromes degree index := by
    apply U64.bv_eq_imp_eq
    exact bits
  refine ⟨first, last, added, subtracted, lastVal, firstVal, ?_, ?_, paid, uncharged, ?_⟩
  · exact ClosedLeaf.inclusive_prefix_normal connection degree bounds.connection
  · have moments := BmRuntimeFrames.inclusive_shared_new syndromes first last (by omega) (by omega)
    change (BmLocatorRuntime.inclusiveRange U64).index ⟨first, last, false⟩ syndromes = _
    simpa only [firstVal, lastVal] using moments
  · rw [reduce, normal, exactOutput]

/-- The original nonzero-discrepancy degree arithmetic, including its two
growth branches. The represented candidate has the stated natural value. -/
theorem degree_candidate_refines (degree index last first : Usize)
    (twiceFits : 2 * degree.val ≤ Usize.max)
    (added : (index + 1#usize : Result Usize) = .ok last)
    (subtracted : (last - degree : Result Usize) = .ok first)
    (firstVal : first.val = index.val + 1 - degree.val) :
    ∃ twice candidate : Usize,
      (2#usize * degree : Result Usize) = .ok twice ∧
      twice.val = 2 * degree.val ∧
      (if twice ≤ index then (do
        let successor ← index + 1#usize
        successor - degree) else Result.ok degree) = .ok candidate ∧
      candidate.val = nextDegree degree index := by
  obtain ⟨twice, doubled, value⟩ := RawMulTable.normal_of_spec _ _
    (Usize.mul_spec (x := 2#usize) (y := degree) (by exact twiceFits))
  change twice.val = 2 * degree.val at value
  have grows : (twice ≤ index) ↔ 2 * degree.val ≤ index.val := by
    rw [UScalar.le_equiv, value]
  by_cases grow : 2 * degree.val ≤ index.val
  · exact ⟨twice, first, doubled, value, by simp only [grows, grow, ite_true, added, bind_ok, subtracted],
      by simp only [nextDegree, grow, ite_true, firstVal]⟩
  · exact ⟨twice, degree, doubled, value, by simp only [grows, grow, ite_false],
      by simp only [nextDegree, grow, ite_false]⟩

theorem even_test (index : Usize) (even : index.val % 2 = 0) :
    core.num.Usize.is_multiple_of index 2#usize = .ok true := by
  change Result.ok (index.val % 2 == 0) = _
  rw [even]
  rfl

theorem even_zero_refines : ActualBmEvenZero := by
  intro K kernels raw reduce back0 back1 back2 tail syndromes budget cost iter meter finalMeter
    connection previous saved degree previousLen shift previousDelta active even bounds charged zero shiftFits
  obtain ⟨first, last, prelude⟩ := prelude_refines kernels raw reduce connection syndromes degree iter.start bounds
  have parity := even_test iter.start even
  by_cases initial : iter.start = 0#usize
  · have test : (iter.start != 0#usize) = false := by simp [initial]
    have sameMeter : finalMeter = meter := by
      have exactMeter := congrArg Prod.snd charged
      simpa [stepCharge, initial] using exactMeter.symm
    simp only [locator_loop0.body, next_active iter active, bind_ok]
    dsimp! only
    simp only [test, Bool.false_eq_true, ite_false, parity, bind_ok, ite_true,
      prelude.coefficients, core.slice.Slice.iter, prelude.nextIndex, prelude.firstIndex,
      core.ops.range.RangeInclusive.new, prelude.moments,
      core.iter.traits.iterator.Iterator.rev.trait_default, core.iter.traits.iterator.Iterator.rev.default,
      core.iter.traits.iterator.Iterator.zip.trait_default, core.iter.traits.iterator.Iterator.zip.default,
      core.iter.traits.collect.IntoIterator.Blanket.into_iter]
    have computed := prelude.firstLoop
    simp only [sourceZip, zipAt] at computed
    simp only [computed, bind_ok]
    dsimp! only
    simp only [prelude.reduced, bind_ok, zero, ite_true, shift_increment shift shiftFits, sameMeter]
  · have test : (iter.start != 0#usize) = true := by simp [initial]
    have charge : meter.charge cost = .ok (.Ok (), finalMeter) := by
      rw [StageCharge.meter_charge_refines]
      simpa only [stepCharge, initial, ite_false] using congrArg Result.ok charged
    simp only [locator_loop0.body, next_active iter active, bind_ok]
    dsimp! only
    simp only [test, ite_true, charge, bind_ok]
    dsimp! only
    simp only [bind_ok, parity, ite_true,
      prelude.coefficients, core.slice.Slice.iter, prelude.nextIndex, prelude.firstIndex,
      core.ops.range.RangeInclusive.new, prelude.moments,
      core.iter.traits.iterator.Iterator.rev.trait_default, core.iter.traits.iterator.Iterator.rev.default,
      core.iter.traits.iterator.Iterator.zip.trait_default, core.iter.traits.iterator.Iterator.zip.default,
      core.iter.traits.collect.IntoIterator.Blanket.into_iter]
    have computed := prelude.paidLoop
    simp only [sourceZip, zipAt] at computed
    simp only [computed, bind_ok]
    dsimp! only
    simp only [prelude.reduced, bind_ok, zero, ite_true, shift_increment shift shiftFits]

theorem degree_exceeds_refines : ActualBmDegreeExceedsBudget := by
  intro K kernels raw reduce back0 back1 back2 tail syndromes budget cost iter meter finalMeter
    connection previous saved degree previousLen shift previousDelta active even bounds charged nonzero twiceFits over
  obtain ⟨first, last, prelude⟩ := prelude_refines kernels raw reduce connection syndromes degree iter.start bounds
  obtain ⟨twice, candidate, doubled, _, candidateNormal, candidateVal⟩ :=
    degree_candidate_refines degree iter.start last first twiceFits prelude.nextIndex prelude.firstIndex prelude.firstVal
  simp only [prelude.nextIndex, prelude.firstIndex, bind_ok] at candidateNormal
  have rejects : budget < candidate := by rw [UScalar.lt_equiv, candidateVal]; exact over
  have parity := even_test iter.start even
  by_cases initial : iter.start = 0#usize
  · have test : (iter.start != 0#usize) = false := by simp [initial]
    have sameMeter : finalMeter = meter := by
      have exactMeter := congrArg Prod.snd charged
      simpa [stepCharge, initial] using exactMeter.symm
    simp only [locator_loop0.body, next_active iter active, bind_ok]
    dsimp! only
    simp only [test, Bool.false_eq_true, ite_false, parity, bind_ok, ite_true,
      prelude.coefficients, core.slice.Slice.iter, prelude.nextIndex, prelude.firstIndex,
      core.ops.range.RangeInclusive.new, prelude.moments,
      core.iter.traits.iterator.Iterator.rev.trait_default, core.iter.traits.iterator.Iterator.rev.default,
      core.iter.traits.iterator.Iterator.zip.trait_default, core.iter.traits.iterator.Iterator.zip.default,
      core.iter.traits.collect.IntoIterator.Blanket.into_iter]
    have computed := prelude.firstLoop
    simp only [sourceZip, zipAt] at computed
    simp only [computed, bind_ok]
    dsimp! only
    simp only [prelude.reduced, bind_ok, nonzero, ite_false, doubled, candidateNormal, rejects,
      ite_true, sameMeter, BmTerminal.joinBuffers]
  · have test : (iter.start != 0#usize) = true := by simp [initial]
    have charge : meter.charge cost = .ok (.Ok (), finalMeter) := by
      rw [StageCharge.meter_charge_refines]
      simpa only [stepCharge, initial, ite_false] using congrArg Result.ok charged
    simp only [locator_loop0.body, next_active iter active, bind_ok]
    dsimp! only
    simp only [test, ite_true, charge, bind_ok]
    dsimp! only
    simp only [bind_ok, parity, ite_true,
      prelude.coefficients, core.slice.Slice.iter, prelude.nextIndex, prelude.firstIndex,
      core.ops.range.RangeInclusive.new, prelude.moments,
      core.iter.traits.iterator.Iterator.rev.trait_default, core.iter.traits.iterator.Iterator.rev.default,
      core.iter.traits.iterator.Iterator.zip.trait_default, core.iter.traits.iterator.Iterator.zip.default,
      core.iter.traits.collect.IntoIterator.Blanket.into_iter]
    have computed := prelude.paidLoop
    simp only [sourceZip, zipAt] at computed
    simp only [computed, bind_ok]
    dsimp! only
    simp only [prelude.reduced, bind_ok, nonzero, ite_false, doubled, candidateNormal, rejects,
      ite_true, BmTerminal.joinBuffers]

end BulksketchBridge.BmEvenStep
