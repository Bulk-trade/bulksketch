import Arithmetic.CandidateRowGenerated
import BulksketchBridge.ClosedLeafWindows
import BulksketchBridge.BmEntry

namespace BulksketchBridge.CandidateNormalization

open Aeneas Aeneas.Std Result DenseCoefficient BmEntry
open bulksketch.sketch.candidates

def offsets (storage : Slice U64) (raw : Usize) : Slice U64 := tail storage (2 * raw.val)

def rowStart (storage : Slice U64) (raw bucket : Usize) : Nat :=
  (offsets storage raw)[bucket.val]!.val

def rowEnd (storage : Slice U64) (raw bucket : Usize) : Nat :=
  (offsets storage raw)[bucket.val + 1]!.val

def RowBounds (storage : Slice U64) (raw bucket : Usize) : Prop :=
  raw ≠ 0#usize →
    2 * raw.val ≤ storage.length ∧ bucket.val + 1 < (offsets storage raw).length ∧
      rowStart storage raw bucket ≤ rowEnd storage raw bucket ∧ rowEnd storage raw bucket ≤ storage.length

def rowView (storage : Slice U64) (raw bucket : Usize) : Slice U64 :=
  if raw = 0#usize then prefixSlice storage 0 else
    ClosedLeaf.region storage (rowStart storage raw bucket) (rowEnd storage raw bucket)

/-- The actual candidate row accessor returns exactly the admitted offset
interval and bypasses offset reads when the request had no candidates. -/
def ActualNativeCandidateRow : Prop :=
  ∀ (storage : Slice U64) (raw bucket : Usize),
    RowBounds storage raw bucket →
    row storage raw bucket = .ok (rowView storage raw bucket)

private theorem suffix_normal (storage : Slice U64) (start : Usize) (room : start.val ≤ storage.length) :
    core.slice.index.SliceIndexRangeFromUsizeSlice.index ⟨start⟩ storage =
      .ok (tail storage start.val) := by
  obtain ⟨suffix, read, exactSuffix, _⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.index.SliceIndexRangeFromUsizeSlice.index.step_spec ⟨start⟩ storage room)
  rw [read]
  exact congrArg Result.ok (Slice.ext _ _ (by simpa only [tail, Slice.from_val] using exactSuffix))

private theorem read_word (words : Slice U64) (index : Usize) (room : index.val < words.length) :
    Slice.index_usize words index = .ok words[index.val]! := by
  obtain ⟨word, read, payload⟩ := RawMulTable.normal_of_spec _ _
    (Slice.index_usize_spec words index room)
  rw [read, payload]
  exact congrArg Result.ok (Slice.Inhabited_getElem_eq_getElem! words index.val room)

private theorem admitted_offset (word : U64) (fits : word.val ≤ Usize.max) :
    ∃ offset : Usize,
      Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from word =
        .ok (.Ok offset) ∧ offset.val = word.val := by
  have bounded : word.val ≤ UScalar.max .Usize := by rw [UScalar.max_USize_eq]; exact fits
  exact checked_unsigned_conversion_normal word bounded

theorem native_candidate_row : ActualNativeCandidateRow := by
  intro storage raw bucket admitted
  by_cases empty : raw = 0#usize
  · have read := RebuiltLfsr.shared_prefix_normal storage 0#usize (by
      rw [show (0#usize).val = 0 from Usize.ofNatCore_val_eq _]; exact Nat.zero_le _)
    simp only [row, rowView, empty, ite_true, core.slice.index.Slice.index, read,
      show (0#usize).val = 0 from Usize.ofNatCore_val_eq _]
  · obtain ⟨prefixRoom, offsetRoom, ordered, endRoom⟩ := admitted empty
    have storageFits : storage.length ≤ Usize.max := storage.length_ineq
    have offsetsFits : (offsets storage raw).length ≤ Usize.max := (offsets storage raw).length_ineq
    have doubleRoom : (2#usize).val * raw.val ≤ Usize.max := by
      rw [show (2#usize).val = 2 from Usize.ofNatCore_val_eq _]
      omega
    obtain ⟨offsetStart, twice, exactPrefix⟩ := RawMulTable.normal_of_spec _ _
      (Usize.mul_spec (x := 2#usize) (y := raw) doubleRoom)
    rw [show (2#usize).val = 2 from Usize.ofNatCore_val_eq _] at exactPrefix
    have offsetSlice := suffix_normal storage offsetStart (by rw [exactPrefix]; exact prefixRoom)
    rw [exactPrefix] at offsetSlice
    change core.slice.index.SliceIndexRangeFromUsizeSlice.index ⟨offsetStart⟩ storage =
      .ok (offsets storage raw) at offsetSlice
    have startRead := read_word (offsets storage raw) bucket (by omega)
    have nextFits : bucket.val + (1#usize).val ≤ Usize.max := by
      rw [show (1#usize).val = 1 from Usize.ofNatCore_val_eq _]
      omega
    obtain ⟨next, nextCall, nextVal⟩ := RawMulTable.normal_of_spec _ _
      (Usize.add_spec (x := bucket) (y := 1#usize) nextFits)
    rw [show (1#usize).val = 1 from Usize.ofNatCore_val_eq _] at nextVal
    have stopRead := read_word (offsets storage raw) next (by rw [nextVal]; exact offsetRoom)
    rw [nextVal] at stopRead
    obtain ⟨start, startCast, startVal⟩ := admitted_offset (offsets storage raw)[bucket.val]!
      (by change rowStart storage raw bucket ≤ Usize.max; omega)
    obtain ⟨stop, stopCast, stopVal⟩ := admitted_offset (offsets storage raw)[bucket.val + 1]!
      (by change rowEnd storage raw bucket ≤ Usize.max; omega)
    change start.val = rowStart storage raw bucket at startVal
    change stop.val = rowEnd storage raw bucket at stopVal
    have read := ClosedLeaf.shared_region_normal storage start stop
      (by rw [startVal, stopVal]; exact ordered) (by rw [stopVal]; exact endRoom)
    simp only [row, rowView, empty, ite_false, twice, bind_ok,
      core.slice.index.Slice.index, offsetSlice, startRead, startCast, nextCall, stopRead, stopCast,
      core.result.Result.expect, read, startVal, stopVal]

/-- An exact accessor transports a packed prefix's distinct and nonzero
properties to the actual row supplied to the native decoder. -/
theorem native_candidate_row_from_packed (storage : Slice U64) (raw bucket : Usize) (used : Nat)
    (admitted : RowBounds storage raw bucket)
    (within : raw ≠ 0#usize → rowEnd storage raw bucket ≤ used)
    (distinct : (prefixSlice storage used).val.Nodup)
    (nonzero : ∀ id ∈ (prefixSlice storage used).val, id ≠ 0#u64) :
    ∃ hints, row storage raw bucket = .ok hints ∧ hints.val.Nodup ∧ ∀ id ∈ hints.val, id ≠ 0#u64 := by
  have sublist : (rowView storage raw bucket).val.Sublist (prefixSlice storage used).val := by
    by_cases empty : raw = 0#usize
    · simp only [rowView, empty, ite_true, prefixSlice, Slice.from_val, List.take_zero]
      exact List.nil_sublist _
    · rw [rowView, ite_eq_right empty, ← ClosedLeaf.region_prefix storage used _ _ (within empty)]
      simp only [ClosedLeaf.region, Slice.from_val, List.slice]
      exact (List.take_sublist _ _).trans (List.drop_sublist _ _)
  exact ⟨rowView storage raw bucket, native_candidate_row storage raw bucket admitted, sublist.nodup distinct,
    fun id present => nonzero id (sublist.subset present)⟩

#print axioms native_candidate_row
#print axioms native_candidate_row_from_packed

end BulksketchBridge.CandidateNormalization
