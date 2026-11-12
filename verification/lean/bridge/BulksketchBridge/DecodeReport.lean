import Arithmetic.DecodeReportGenerated
import BulksketchBridge.PublicationWrite
import BulksketchBridge.ClosedLeafWindows

namespace BulksketchBridge.DecodeReport

open Aeneas Aeneas.Std Result Error
open bulksketch.sketch.api bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 2100000

def decoded (ids : Slice U64) (start len : U64) : Result (Option DecodeOutcome) :=
  if start.val ≤ UScalar.max .Usize ∧ len.val ≤ UScalar.max .Usize then
    if start.val + len.val ≤ UScalar.max .Usize then
      if start.val + len.val ≤ ids.length then
        .ok (some (.Decoded (ClosedLeaf.region ids start.val (start.val + len.val))))
      else .fail .panic
    else .fail .integerOverflow
  else .fail .panic

def row (ids : Slice U64) (value : StoredOutcome) : Result (Option DecodeOutcome) :=
  match value.status with
  | .Unset => .fail .panic
  | .Equal => .ok (some .Equal)
  | .Decoded => decoded ids value.start value.len
  | .DegreeExceedsBudget => .ok (some (.Failed .DegreeExceedsBudget))
  | .InvalidLocator => .ok (some (.Failed .InvalidLocator))
  | .NotSplit => .ok (some (.Failed .NotSplit))
  | .VerificationFailed => .ok (some (.Failed .VerificationFailed))

def expectedOutcome (self : DecodeReport) (bucket : Usize) : Result (Option DecodeOutcome) :=
  match self.outcomes.val[bucket.val]? with
  | none => .ok none
  | some value => row self.ids value

private theorem decoded_refines (ids : Slice U64) (start len : U64)
    (offsetMsg lengthMsg : Str) :
    (do
      let firstResult ← Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from start
      let first ← core.result.Result.expect bulksketch.core.num.error.TryFromIntError.Insts.CoreFmtDebug firstResult offsetMsg
      let lenResult ← Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from len
      let count ← core.result.Result.expect bulksketch.core.num.error.TryFromIntError.Insts.CoreFmtDebug lenResult lengthMsg
      let stop ← first + count
      let words ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U64)
        ids { start := first, «end» := stop }
      .ok (some (DecodeOutcome.Decoded words))) = decoded ids start len := by
  by_cases firstFits : start.val ≤ UScalar.max .Usize
  · by_cases countFits : len.val ≤ UScalar.max .Usize
    · obtain ⟨first, firstNormal, firstVal⟩ :=
        checked_unsigned_conversion_normal (target := .Usize) start firstFits
      obtain ⟨count, countNormal, countVal⟩ :=
        checked_unsigned_conversion_normal (target := .Usize) len countFits
      change core.num.tryFromUScalar .Usize start = _ at firstNormal
      change core.num.tryFromUScalar .Usize len = _ at countNormal
      simp only [Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from, firstNormal, countNormal,
        bind_ok, core.result.Result.expect, decoded, firstFits, countFits, and_self, ite_true]
      by_cases endFits : start.val + len.val ≤ UScalar.max .Usize
      · obtain ⟨stop, add, stopVal⟩ := RawMulTable.normal_of_spec _ _
          (Usize.add_spec (x := first) (y := count) (by rwa [firstVal, countVal, ← UScalar.max_USize_eq]))
        change stop.val = first.val + count.val at stopVal
        have exactStop : stop.val = start.val + len.val := by rw [stopVal, firstVal, countVal]
        have ordered : first.val ≤ stop.val := by omega
        simp only [add, bind_ok, endFits, ite_true, Slice.index_SliceIndexRangeUsizeSliceInst]
        by_cases room : start.val + len.val ≤ ids.length
        · rw [ClosedLeaf.shared_region_normal ids first stop ordered (by rwa [exactStop]),
              bind_ok, firstVal, exactStop, ite_eq_left room]
        · have outside : ¬ (first ≤ stop ∧ stop ≤ ids.length) := by
            intro valid
            have lenFit : stop.val ≤ ids.length := valid.2
            omega
          simp only [core.slice.index.SliceIndexRangeUsizeSlice.index, outside,
            ite_false, bind_fail, room]
      · have add : (first + count : Result Usize) = .fail .integerOverflow := by
          change UScalar.tryMk .Usize (first.val + count.val) = _
          have overflow : ¬UScalar.inBounds .Usize (first.val + count.val) := by
            rw [UScalar.inBounds, firstVal, countVal]
            simp only [UScalar.max] at endFits
            omega
          have bad : ¬UScalar.check_bounds .Usize (first.val + count.val) := fun checked =>
            overflow (UScalar.check_bounds_imp_inBounds checked)
          simp only [UScalar.tryMk, UScalar.tryMkOpt, dite_eq_right bad, Result.ofOption]
        simp only [add, endFits, ite_false, bind_fail]
    · have failed : core.num.tryFromUScalar .Usize len = .ok (.Err ()) := by
        rw [core.num.tryFromUScalar, ite_eq_right countFits]
      obtain ⟨first, normal, _⟩ := checked_unsigned_conversion_normal (target := .Usize) start firstFits
      simp only [Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from, normal, failed,
        bind_ok, core.result.Result.expect, bind_fail, decoded, countFits, and_false, ite_false]
  · have failed : core.num.tryFromUScalar .Usize start = .ok (.Err ()) := by
      rw [core.num.tryFromUScalar, ite_eq_right firstFits]
    simp only [Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from, failed,
      bind_ok, core.result.Result.expect, bind_fail, decoded, firstFits, false_and, ite_false]

/-- The original public row accessor reports absent and failed rows
exactly, and returns the admitted original ID subview for decoded rows. -/
def ActualDecodeReportOutcome : Prop :=
  ∀ (self : DecodeReport) (bucket : Usize),
    DecodeReport.outcome self bucket = expectedOutcome self bucket

theorem outcome_refines : ActualDecodeReportOutcome := by
  intro self bucket
  have get : core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice StoredOutcome) self.outcomes bucket =
      .ok (self.outcomes.val[bucket.val]?) := rfl
  unfold DecodeReport.outcome expectedOutcome
  rw [get, bind_ok]
  cases record : self.outcomes.val[bucket.val]? with
  | none =>
    simp only [bulksketch.core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok,
      bulksketch.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
  | some stored =>
    simp only [bulksketch.core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok]
    cases tag : stored.status <;> simp only [row, tag]
    exact decoded_refines self.ids stored.start stored.len _ _

def ActualDecodeReportBucketCount : Prop :=
  ∀ self : DecodeReport, DecodeReport.bucket_count self = .ok self.outcomes.len

theorem bucket_count_refines : ActualDecodeReportBucketCount := fun _ => rfl

#print axioms outcome_refines
#print axioms bucket_count_refines

end BulksketchBridge.DecodeReport
