import BulksketchBridge.AvxSquareBlocks

namespace BulksketchBridge.AvxSquare

open Aeneas Aeneas.Std Aeneas.Std.AvxSquareRuntime
open bulksketch.backend.x86_vpclmul512
open scoped BulksketchBridge.DenseMulReductionSpec

set_option maxRecDepth 4096

theorem ceil_half (degree : Usize) :
    ∃ result : Usize, bulksketch.DenseReducerSquareRuntime.divCeil degree 2#usize = .ok result ∧
      result.val = (degree.val + 1) / 2 := by
  obtain ⟨quotient, divNormal, divVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.div_spec degree (y := 2#usize) (by simp))
  obtain ⟨remainder, remNormal, remVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.rem_spec degree (y := 2#usize) (by simp))
  change quotient.val = degree.val / 2 at divVal
  change remainder.val = degree.val % 2 at remVal
  have max : degree.val ≤ Usize.max := by scalar_tac
  simp only [bulksketch.DenseReducerSquareRuntime.divCeil, divNormal, remNormal, bind_ok, UScalar.lt_equiv]
  change ∃ result, (if 0 < remainder.val then quotient + 1#usize else .ok quotient) =
    .ok result ∧ result.val = (degree.val + 1) / 2
  by_cases hasRemainder : 0 < remainder.val
  · obtain ⟨successor, added, value⟩ := RawMulTable.normal_of_spec _ _
      (Usize.add_spec (x := quotient) (y := 1#usize) (by change quotient.val + 1 ≤ Usize.max; omega))
    change successor.val = quotient.val + 1 at value
    exact ⟨successor, by simp only [hasRemainder, ite_true, added], by omega⟩
  · exact ⟨quotient, by simp only [hasRemainder, ite_false], by omega⟩

@[simp] theorem seed_dst_length (input : Slice U64) (index firstHigh : Nat)
    (dst : Slice U64) (scratch : Slice Raw) (count : Nat) :
    (seed input index firstHigh dst scratch count).1.length = dst.length := by
  induction count generalizing index dst scratch with
  | zero => rfl
  | succ n ih => simp only [seed, ih, seed_step_dst_length]

@[simp] theorem seed_scratch_length (input : Slice U64) (index firstHigh : Nat)
    (dst : Slice U64) (scratch : Slice Raw) (count : Nat) :
    (seed input index firstHigh dst scratch count).2.length = scratch.length := by
  induction count generalizing index dst scratch with
  | zero => rfl
  | succ n ih => simp only [seed, ih, seed_step_scratch_length]

def squareResult (input table dst : Slice U64) (scratch : Slice Raw) : Slice U64 × Slice Raw :=
  let degree := dst.length
  let firstHigh := (degree + 1) / 2
  let (seeded, squared) := seed input 0 firstHigh (RebuiltLfsr.zeroWords dst) scratch input.length
  (scanBlocks (DenseMul.takeSlice squared input.length) table degree firstHigh 0 seeded degree, squared)

/-- Original accelerated square under explicitly supplied masked slice
memory operations, including both final mutable slices. -/
def ActualAvxSquare : Prop :=
  ∀ (loadModel : Load) (storeModel : Store), LoadLaw loadModel → StoreLaw storeModel →
    ∀ (input table dst : Slice U64) (scratch : Slice Raw),
      input.length ≤ dst.length → input.length ≤ scratch.length →
      dst.length + 8 ≤ Usize.max →
      dst.length / 2 * dst.length ≤ table.length →
      square_mod loadModel storeModel input table dst scratch = .ok (squareResult input table dst scratch)

theorem square_mod_refines : ActualAvxSquare := by
  intro loadModel storeModel loadLaw storeLaw input table dst scratch aBound scratchRoom safe tableRoom
  let degree := Slice.len dst
  have degreeVal : degree.val = dst.length := Slice.len_val dst
  obtain ⟨firstHigh, ceil, firstHighVal⟩ := ceil_half degree
  let zeros := RebuiltLfsr.zeroWords dst
  have zeroLength : zeros.length = dst.length := by simp [zeros, RebuiltLfsr.zeroWords, Slice.length]
  let prepared := seed input 0 firstHigh.val zeros scratch input.length
  have preparedDst : prepared.1.length = degree.val := by simp [prepared, zeroLength, degreeVal]
  have preparedRaw : prepared.2.length = scratch.length := by simp [prepared]
  have seeded := seed_loop_refines input zeros scratch 0#usize firstHigh scratchRoom
    (by rw [firstHighVal, degreeVal, zeroLength]) (by simp)
  simp only [show (0#usize).val = 0 by simp, Nat.sub_zero] at seeded
  have scanned := block_loop_refines loadModel storeModel loadLaw storeLaw input table prepared.1 prepared.2
    0#usize degree firstHigh (by rwa [degreeVal]) (by rwa [degreeVal]) (by rwa [preparedRaw])
    firstHighVal preparedDst (by rwa [degreeVal]) degree.val (by simp)
  simp only [square_mod, show bulksketch.DenseReducerSquareRuntime.divCeil (Slice.len dst) 2#usize = _ from ceil,
    bind_ok, RebuiltLfsr.fill_zero, core.slice.Slice.iter,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default]
  change (do
    let (out, raw) ← square_mod_loop0 (enumerateAt input 0#usize) zeros scratch firstHigh
    let iter ← core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» := degree } 8#usize
    let final ← square_mod_loop1 loadModel storeModel iter input table out raw degree firstHigh
    .ok (final, raw)) = _
  rw [seeded]
  simp only [Bind.bind, bind_ok]
  change (do
    let iter ← core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» := degree } 8#usize
    let final ← square_mod_loop1 loadModel storeModel iter input table prepared.1 prepared.2 degree firstHigh
    .ok (final, prepared.2)) = _
  have range : core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» := degree } 8#usize = .ok (blockAt 0#usize degree) := rfl
  simp only [range, Bind.bind, bind_ok, scanned, show (0#usize).val = 0 by simp, squareResult]
  simp only [prepared, zeros, firstHighVal, degreeVal]

theorem square_result_lengths (input table dst : Slice U64) (scratch : Slice Raw) :
    (squareResult input table dst scratch).1.length = dst.length ∧
    (squareResult input table dst scratch).2.length = scratch.length := by
  simp [squareResult, RebuiltLfsr.zeroWords, Slice.length, seed_dst_length, seed_scratch_length]

end BulksketchBridge.AvxSquare
