import BulksketchBridge.AvxSquareRows
import BulksketchBridge.DenseMul

namespace BulksketchBridge.AvxSquare

open Aeneas Aeneas.Std Aeneas.Std.Avx512Register Aeneas.Std.AvxSquareRuntime
open BulksketchBridge.Avx512RegisterChallenges
open bulksketch.backend.x86_vpclmul512
open scoped BulksketchBridge.DenseMulReductionSpec

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

abbrev BlockIter := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)

def blockAt (offset degree : Usize) : BlockIter := ⟨⟨offset, degree⟩, 8#usize⟩

private theorem block_active (offset degree : Usize) (active : offset.val < degree.val) :
    ∃ next : Usize, next.val = min (offset.val + 8) degree.val ∧
      core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) (blockAt offset degree) =
        .ok (some offset, blockAt next degree) := by
  obtain ⟨⟨item, state⟩, normal, values⟩ := RawMulTable.normal_of_spec _ _
    (core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec (blockAt offset degree) (by simp [blockAt]))
  rcases (show (item = some offset ∧ state.iter.start.val = min (offset.val + 8) degree.val) ∧
      state.iter.end = degree ∧ state.step_by = 8#usize from by simpa [blockAt, active] using values)
    with ⟨⟨itemValue, nextValue⟩, endValue, strideValue⟩
  have same : state = blockAt state.iter.start degree := by
    rcases state with ⟨⟨start, stop⟩, stride⟩
    simp_all [blockAt]
  exact ⟨state.iter.start, nextValue, by rw [normal, itemValue]; exact congrArg (fun t => Result.ok (some offset, t)) same⟩

private theorem block_done (offset degree : Usize) (done : degree.val ≤ offset.val) :
    ∃ terminal : BlockIter,
      core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) (blockAt offset degree) =
        .ok (none, terminal) := by
  obtain ⟨⟨item, state⟩, normal, values⟩ := RawMulTable.normal_of_spec _ _
    (core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec (blockAt offset degree) (by simp [blockAt]))
  have itemValue : item = none := by
    have notActive : ¬offset.val < degree.val := by omega
    have caseValues : (item = none ∧ state.iter.start = offset) ∧
        state.iter.end = degree ∧ state.step_by = 8#usize := by
      simpa [blockAt, notActive] using values
    exact caseValues.1.1
  exact ⟨state, by rwa [itemValue] at normal⟩

private theorem raw_prefix (scratch : Slice Raw) (stop : Usize) (bound : stop.val ≤ scratch.length) :
    core.slice.index.SliceIndexRangeToUsizeSlice.index ⟨stop⟩ scratch =
      .ok (DenseMul.takeSlice scratch stop.val) := by
  obtain ⟨window, normal, values, _⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec ⟨stop⟩ scratch bound)
  rw [normal]
  exact congrArg Result.ok (Slice.ext _ _ (by simpa only [DenseMul.takeSlice, Slice.from_val, List.slice_zero_j] using values))

def reduceRegisters (even odd : Word512) : Word512 :=
  fun pair half =>
    let product := if half then odd else even
    BulksketchProofs.Field.reduceFold64 (product pair false) (product pair true)

private theorem unpack_reduce (even odd : Word512) :
    shiftedReduction (fun pair high => if high then odd pair false else even pair false)
      (fun pair high => if high then odd pair true else even pair true) = reduceRegisters even odd := by
  funext pair half
  cases half <;> rfl

def blockStep (scratch : Slice Raw) (table : Slice U64) (degree firstHigh offset stop : Nat)
    (dst : Slice U64) : Slice U64 :=
  let zero : Word512 := fun _ _ => 0
  let accum := scanRows scratch table degree firstHigh firstHigh offset stop zero zero
    (scratch.length - firstHigh)
  let out := ClosedLeaf.region dst offset stop
  if bound : out.length ≤ 8 then
    let stored := storeWords out (xorRegister (loadWords out) (reduceRegisters accum.1 accum.2)) bound
    dst.setSlice! offset stored.val
  else dst

def scanBlocks (scratch : Slice Raw) (table : Slice U64) (degree firstHigh offset : Nat)
    (dst : Slice U64) : Nat → Slice U64
  | 0 => dst
  | fuel + 1 =>
    if offset < degree then
      let stop := min (offset + 8) degree
      scanBlocks scratch table degree firstHigh stop
        (blockStep scratch table degree firstHigh offset stop dst) fuel
    else dst

@[simp] theorem blockStep_length (scratch : Slice Raw) (table : Slice U64)
    (degree firstHigh offset stop : Nat) (dst : Slice U64) :
    (blockStep scratch table degree firstHigh offset stop dst).length = dst.length := by
  unfold blockStep
  dsimp only
  split <;> simp only [Slice.setSlice!_length]

@[simp] theorem scanBlocks_length (scratch : Slice Raw) (table : Slice U64)
    (degree firstHigh offset : Nat) (dst : Slice U64) (fuel : Nat) :
    (scanBlocks scratch table degree firstHigh offset dst fuel).length = dst.length := by
  induction fuel generalizing offset dst with
  | zero => rfl
  | succ fuel ih => by_cases active : offset < degree <;> simp only [scanBlocks, active, ite_true, ite_false, ih, blockStep_length]

/-- Exact original outer block body, including the final short block and
the writeback returned by the destination subslice. -/
theorem block_body_active (loadModel : Load) (storeModel : Store)
    (loadLaw : LoadLaw loadModel) (storeLaw : StoreLaw storeModel)
    (input table dst : Slice U64) (scratch : Slice Raw) (offset degree firstHigh : Usize)
    (active : offset.val < degree.val) (safe : degree.val + 8 ≤ Usize.max)
    (aBound : input.length ≤ degree.val) (scratchRoom : input.length ≤ scratch.length)
    (firstHighVal : firstHigh.val = (degree.val + 1) / 2)
    (dstLen : dst.length = degree.val) (tableBound : degree.val / 2 * degree.val ≤ table.length) :
    ∃ next : Usize, next.val = min (offset.val + 8) degree.val ∧
      square_mod_loop1.body loadModel storeModel input table scratch degree firstHigh (blockAt offset degree) dst =
        .ok (.cont (blockAt next degree, blockStep (DenseMul.takeSlice scratch input.length) table
          degree.val firstHigh.val offset.val next.val dst)) := by
  obtain ⟨next, nextValue, iteration⟩ := block_active offset degree active
  obtain ⟨end8, add8, end8Val⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := offset) (y := 8#usize) (by change offset.val + 8 ≤ Usize.max; omega))
  change end8.val = offset.val + 8 at end8Val
  let stop := core.cmp.impls.OrdUsize.min end8 degree
  have stopVal : stop.val = next.val := by simp only [stop, core.cmp.impls.OrdUsize.min_val, end8Val, nextValue]
  have stopEq : stop = next := UScalar.eq_of_val_eq stopVal
  have endBound : next.val ≤ degree.val := by omega
  have ordered : offset.val ≤ next.val := by omega
  have limited : next.val - offset.val ≤ 8 := by omega
  have prefixNormal := raw_prefix scratch (Slice.len input) (by simpa only [Slice.len_val] using scratchRoom)
  let front := DenseMul.takeSlice scratch input.length
  have frontLen : front.length = input.length := by simp only [front, DenseMul.take_length, Nat.min_eq_left scratchRoom]
  let zero : Word512 := fun _ _ => 0
  have scan := high_loop_refines loadModel loadLaw front table degree firstHigh offset next 0#usize firstHigh
    zero zero (by simp) (by simp) firstHighVal (by omega) ⟨ordered, endBound, limited⟩ tableBound
  let out := ClosedLeaf.region dst offset.val next.val
  have outLen : out.length = next.val - offset.val :=
    ClosedLeaf.region_length dst offset.val next.val (by omega)
  have outBound : out.length ≤ 8 := by omega
  have cut := ClosedLeaf.mutable_region_normal dst offset next ordered (by omega)
  refine ⟨next, nextValue, ?_⟩
  simp only [square_mod_loop1.body, iteration, bind_ok]
  dsimp! only
  simp only [add8, bind_ok, lift, show core.cmp.impls.OrdUsize.min end8 degree = next from stopEq,
    AvxSquareRuntime.zero, Slice.index_SliceIndexRangeToUsizeSliceInst, prefixNormal, Slice.len_val,
    core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default, AvxSquareRuntime.skip, bind_ok]
  have skipShape : (⟨⟨⟨front, 0⟩, 0#usize⟩, firstHigh⟩ : Skip (Enumerate Raw)) = skipAt front 0#usize firstHigh := rfl
  rw [skipShape, scan]
  simp only [bind_ok]
  dsimp! only
  simp only [unpack, bind_ok, Slice.index_mut_SliceIndexRangeUsizeSliceInst, cut]
  rw [Avx512Register.reduce_shift_refines _ _]
  simp only [bind_ok]
  dsimp! only
  simp only [loadLaw (ClosedLeaf.region dst offset.val next.val) outBound, xorWords, bind_ok]
  rw [storeLaw (ClosedLeaf.region dst offset.val next.val) _ outBound]
  simp only [bind_ok, blockStep, show (0#usize).val = 0 by simp, Nat.zero_add, dite_eq_left (show (ClosedLeaf.region dst offset.val next.val).length ≤ 8 from outBound), unpack_reduce, xorRegister]
  rfl

theorem block_loop_refines (loadModel : Load) (storeModel : Store)
    (loadLaw : LoadLaw loadModel) (storeLaw : StoreLaw storeModel)
    (input table dst : Slice U64) (scratch : Slice Raw) (offset degree firstHigh : Usize)
    (safe : degree.val + 8 ≤ Usize.max)
    (aBound : input.length ≤ degree.val) (scratchRoom : input.length ≤ scratch.length)
    (firstHighVal : firstHigh.val = (degree.val + 1) / 2)
    (dstLen : dst.length = degree.val) (tableBound : degree.val / 2 * degree.val ≤ table.length)
    (fuel : Nat) (enough : degree.val - offset.val ≤ fuel) :
    square_mod_loop1 loadModel storeModel (blockAt offset degree) input table dst scratch degree firstHigh =
      .ok (scanBlocks (DenseMul.takeSlice scratch input.length) table degree.val firstHigh.val offset.val dst fuel) := by
  induction fuel generalizing offset dst with
  | zero =>
    have done : degree.val ≤ offset.val := by omega
    obtain ⟨terminal, exhausted⟩ := block_done offset degree done
    have body : square_mod_loop1.body loadModel storeModel input table scratch degree firstHigh (blockAt offset degree) dst =
      .ok (.done dst) := by
        simp only [square_mod_loop1.body, exhausted, bind_ok]
        rfl
    rw [scanBlocks]
    conv => lhs; unfold square_mod_loop1 loop
    dsimp only
    rw [body, bind_ok]
  | succ fuel ih =>
    by_cases active : offset.val < degree.val
    · obtain ⟨next, nextValue, body⟩ := block_body_active loadModel storeModel loadLaw storeLaw
        input table dst scratch offset degree firstHigh active safe aBound scratchRoom firstHighVal dstLen tableBound
      let updated := blockStep (DenseMul.takeSlice scratch input.length) table degree.val firstHigh.val offset.val next.val dst
      simp only [scanBlocks, active, ite_true, ← nextValue]
      conv => lhs; unfold square_mod_loop1 loop
      dsimp only
      rw [body]
      simp only [bind_ok]
      change square_mod_loop1 loadModel storeModel (blockAt next degree) input table updated scratch degree firstHigh = _
      apply ih updated next (by simpa [updated])
      omega
    · obtain ⟨terminal, exhausted⟩ := block_done offset degree (by omega)
      have body : square_mod_loop1.body loadModel storeModel input table scratch degree firstHigh (blockAt offset degree) dst =
        .ok (.done dst) := by
          simp only [square_mod_loop1.body, exhausted, bind_ok]
          rfl
      simp only [scanBlocks, active, ite_false]
      conv => lhs; unfold square_mod_loop1 loop
      dsimp only
      rw [body, bind_ok]

end BulksketchBridge.AvxSquare
