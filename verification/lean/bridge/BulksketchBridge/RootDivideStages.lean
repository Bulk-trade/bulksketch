import BulksketchBridge.RootDivideSpec
import BulksketchBridge.RootSetup
import BulksketchBridge.BmEntry
import BulksketchBridge.ClosedLeafWindows

namespace BulksketchBridge.RootDivide

open Aeneas Aeneas.Std Result Error
open Aeneas.Std.RootDivideRuntime
open DenseCoefficient RebuiltLfsr BmEntry
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem first_charge_failure (exactDivision : ExactDivide) {F K : Type}
    (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (roots : Roots) (buffers : FactorWork) (factors : Slice U64) (stack : Slice FactorFrame)
    (meter finalMeter : WorkMeter) (error : DecodeError)
    (charged : charge meter (.Divide roots.degree) = .ok (.Err error, finalMeter)) :
    Roots.divide exactDivision field kernels roots buffers factors stack meter =
      .ok (unchanged roots buffers factors stack finalMeter (.Err error)) := by
  simp only [Roots.divide, charged, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from, unchanged]
  dsimp! only
  simp only [bind_ok]
  all_goals first | rfl | (simp only [Bind.bind, bind_ok, id_eq]; rfl)

private theorem call_prelude (roots : Roots) (buffers : FactorWork)
    (workRoom : roots.degree.val + 2 ≤ buffers.work.length) (gcdRoom : roots.gcd_len.val ≤ buffers.gcd.length) :
    ∃ width : Usize,
      (roots.degree + 2#usize : Result Usize) = .ok width ∧
      core.slice.Slice.split_at_mut buffers.work width = .ok
        ((prefixSlice buffers.work (roots.degree.val + 2), tail buffers.work (roots.degree.val + 2)),
          splitBack buffers.work (roots.degree.val + 2)) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U64)
        buffers.gcd { «end» := roots.gcd_len } = .ok (prefixSlice buffers.gcd roots.gcd_len.val) := by
  have bound : buffers.work.length ≤ Usize.max := buffers.work.length_ineq
  obtain ⟨width, normal, value⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := roots.degree) (y := 2#usize) (by change roots.degree.val + 2 ≤ Usize.max; omega))
  change width.val = roots.degree.val + 2 at value
  have split := split_refines buffers.work width (by omega)
  rw [value] at split
  exact ⟨width, normal, split, by
    rw [Slice.index_SliceIndexRangeToUsizeSliceInst, shared_prefix_normal _ _ gcdRoom]⟩

theorem nonexact_failure (exactDivision : ExactDivide) {F K : Type}
    (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (roots : Roots) (buffers : FactorWork) (factors : Slice U64) (stack : Slice FactorFrame)
    (meter paid : WorkMeter) (quotient remainder : Slice U64) (raw : Slice RawProduct)
    (workRoom : roots.degree.val + 2 ≤ buffers.work.length) (gcdRoom : roots.gcd_len.val ≤ buffers.gcd.length)
    (charged : charge meter (.Divide roots.degree) = .ok (.Ok (), paid))
    (call : reached exactDivision field kernels roots buffers none quotient remainder raw) :
    Roots.divide exactDivision field kernels roots buffers factors stack meter =
      .ok (unchanged roots (afterCall roots buffers quotient remainder raw) factors stack paid (.Ok (.Err .InvalidLocator))) := by
  obtain ⟨width, added, split, divisor⟩ := call_prelude roots buffers workRoom gcdRoom
  simp only [Roots.divide, charged, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  dsimp! only
  simp only [added, split, bind_ok]
  dsimp! only
  simp only [divisor, bind_ok, reached] at call ⊢
  rw [call]
  simp only [bind_ok, unchanged, afterCall]
  all_goals first | rfl | (simp only [Bind.bind, bind_ok, id_eq]; rfl)

theorem assembly_charge_failure (exactDivision : ExactDivide) {F K : Type}
    (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (roots : Roots) (buffers : FactorWork) (factors : Slice U64) (stack : Slice FactorFrame)
    (meter paid finalMeter : WorkMeter) (length : Usize) (quotient remainder : Slice U64) (raw : Slice RawProduct)
    (error : DecodeError) (workRoom : roots.degree.val + 2 ≤ buffers.work.length) (gcdRoom : roots.gcd_len.val ≤ buffers.gcd.length)
    (charged : charge meter (.Divide roots.degree) = .ok (.Ok (), paid))
    (call : reached exactDivision field kernels roots buffers (some length) quotient remainder raw)
    (assembly : charge paid (.SplitAssembly roots.degree) = .ok (.Err error, finalMeter)) :
    Roots.divide exactDivision field kernels roots buffers factors stack meter =
      .ok (unchanged roots (afterCall roots buffers quotient remainder raw) factors stack finalMeter (.Err error)) := by
  obtain ⟨width, added, split, divisor⟩ := call_prelude roots buffers workRoom gcdRoom
  simp only [Roots.divide, charged, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  dsimp! only
  simp only [added, split, bind_ok]
  dsimp! only
  simp only [divisor, bind_ok, reached] at call ⊢
  rw [call]
  simp only [bind_ok, assembly, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
    unchanged, afterCall]
  dsimp! only
  simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
  all_goals first | rfl | (simp only [Bind.bind, bind_ok, id_eq]; rfl)

theorem offset_overflow (exactDivision : ExactDivide) {F K : Type}
    (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (roots : Roots) (buffers : FactorWork) (factors : Slice U64) (stack : Slice FactorFrame)
    (meter paid finalMeter : WorkMeter) (length : Usize) (quotient remainder : Slice U64) (raw : Slice RawProduct)
    (workRoom : roots.degree.val + 2 ≤ buffers.work.length) (gcdRoom : roots.gcd_len.val ≤ buffers.gcd.length)
    (charged : charge meter (.Divide roots.degree) = .ok (.Ok (), paid))
    (call : reached exactDivision field kernels roots buffers (some length) quotient remainder raw)
    (assembly : charge paid (.SplitAssembly roots.degree) = .ok (.Ok (), finalMeter))
    (overflow : Usize.checked_mul roots.pending roots.stride = none) :
    Roots.divide exactDivision field kernels roots buffers factors stack meter =
      .ok (unchanged roots (afterCall roots buffers quotient remainder raw) factors stack
        finalMeter (.Err .ScratchTooSmall)) := by
  obtain ⟨width, added, split, divisor⟩ := call_prelude roots buffers workRoom gcdRoom
  simp only [Roots.divide, charged, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  dsimp! only
  simp only [added, split, bind_ok]
  dsimp! only
  simp only [divisor, bind_ok, reached] at call ⊢
  rw [call]
  simp only [bind_ok, assembly, core.result.Result.Insts.CoreOpsTry.branch, unchanged, afterCall]
  dsimp! only
  simp only [lift, bind_ok, overflow, core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from, Bind.bind]
  all_goals rfl


theorem endpoint_overflow (exactDivision : ExactDivide) {F K : Type}
    (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (roots : Roots) (buffers : FactorWork) (factors : Slice U64) (stack : Slice FactorFrame)
    (meter paid finalMeter : WorkMeter) (length start : Usize) (quotient remainder : Slice U64) (raw : Slice RawProduct)
    (workRoom : roots.degree.val + 2 ≤ buffers.work.length) (gcdRoom : roots.gcd_len.val ≤ buffers.gcd.length)
    (charged : charge meter (.Divide roots.degree) = .ok (.Ok (), paid))
    (call : reached exactDivision field kernels roots buffers (some length) quotient remainder raw)
    (assembly : charge paid (.SplitAssembly roots.degree) = .ok (.Ok (), finalMeter))
    (startOk : Usize.checked_mul roots.pending roots.stride = some start)
    (overflow : Usize.checked_add start length = none) :
    Roots.divide exactDivision field kernels roots buffers factors stack meter =
      .ok (unchanged roots (afterCall roots buffers quotient remainder raw) factors stack
        finalMeter (.Err .ScratchTooSmall)) := by
  obtain ⟨width, added, split, divisor⟩ := call_prelude roots buffers workRoom gcdRoom
  simp only [Roots.divide, charged, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  dsimp! only
  simp only [added, split, bind_ok]
  dsimp! only
  simp only [divisor, bind_ok, reached] at call ⊢
  rw [call]
  simp only [bind_ok, assembly, core.result.Result.Insts.CoreOpsTry.branch, unchanged, afterCall]
  dsimp! only
  simp only [lift, bind_ok, startOk, overflow, core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from, Bind.bind]
  all_goals rfl


/-- Successful original non-affine assembly writes the pending right
factor and slot before the left modulus replacement and stage dispatch. -/
theorem commit_nonaffine (exactDivision : ExactDivide) {F K : Type}
    (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (roots : Roots) (buffers : FactorWork) (factors : Slice U64) (stack : Slice FactorFrame)
    (meter paid finalMeter : WorkMeter) (length start stop pending : Usize)
    (startWord lengthWord : U64) (direction : U32) (quotient remainder : Slice U64) (raw : Slice RawProduct)
    (workRoom : roots.degree.val + 2 ≤ buffers.work.length)
    (gcdRoom : roots.gcd_len.val ≤ buffers.gcd.length)
    (charged : charge meter (.Divide roots.degree) = .ok (.Ok (), paid))
    (call : reached exactDivision field kernels roots buffers (some length) quotient remainder raw)
    (assembly : charge paid (.SplitAssembly roots.degree) = .ok (.Ok (), finalMeter))
    (startOk : Usize.checked_mul roots.pending roots.stride = some start)
    (endOk : Usize.checked_add start length = some stop)
    (endpoint : stop.val = start.val + length.val) (factorRoom : stop.val ≤ factors.length)
    (quotientRoom : length.val ≤ quotient.length) (slotRoom : roots.pending.val < stack.length)
    (modulusRoom : roots.gcd_len.val ≤ buffers.modulus.length)
    (startCast : U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from start = .ok (.Ok startWord))
    (lengthCast : U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from length = .ok (.Ok lengthWord))
    (directionOk : (roots.direction + 1#u32 : Result U32) = .ok direction)
    (pendingOk : (roots.pending + 1#usize : Result Usize) = .ok pending)
    (nonaffine : roots.affine = false) :
    let updated := { roots with pending := pending, degree := roots.gcd_degree, direction := direction, checked := true }
    let buffers' := { afterCall roots buffers quotient remainder raw with
      modulus := restorePrefix buffers.modulus (prefixSlice buffers.gcd roots.gcd_len.val) }
    let factors' := factors.setSlice! start.val (prefixSlice quotient length.val).val
    let frame : FactorFrame := ⟨startWord, lengthWord, direction, 1#u32⟩
    Roots.divide exactDivision field kernels roots buffers factors stack meter =
      .ok (.Ok (.Ok (ClosedLeafAdvance.stageFor updated)), updated, buffers', id,
        factors', stack.set roots.pending frame, finalMeter) := by
  obtain ⟨width, added, split, divisor⟩ := call_prelude roots buffers workRoom gcdRoom
  have factorCut := ClosedLeaf.mutable_region_normal factors start stop (by omega) factorRoom
  have quotientCut := shared_prefix_normal quotient length quotientRoom
  have factorsCopy := ClosedLeaf.copy_normal
    (ClosedLeaf.region factors start.val stop.val) (prefixSlice quotient length.val) (by
      rw [ClosedLeaf.region_length _ _ _ factorRoom, prefix_length, Nat.min_eq_left quotientRoom, endpoint]
      omega)
  have modulusCut := prefix_normal buffers.modulus roots.gcd_len modulusRoom
  have modulusCopy := ClosedLeaf.copy_normal
    (prefixSlice buffers.modulus roots.gcd_len.val) (prefixSlice buffers.gcd roots.gcd_len.val) (by
      rw [prefix_length, Nat.min_eq_left modulusRoom, prefix_length, Nat.min_eq_left gcdRoom])
  obtain ⟨⟨old, back⟩, stackCut, _, backExact⟩ := RawMulTable.normal_of_spec _ _
    (Slice.index_mut_usize_spec stack roots.pending slotRoom)
  rw [backExact] at stackCut
  simp only [Roots.divide, charged, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  dsimp! only
  simp only [added, split, bind_ok]
  dsimp! only
  simp only [divisor, bind_ok, reached] at call ⊢
  rw [call]
  simp only [bind_ok, assembly, core.result.Result.Insts.CoreOpsTry.branch]
  dsimp! only
  simp only [lift, bind_ok, startOk, endOk, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch]
  simp only [core.slice.index.Slice.index_mut, factorCut, Slice.index_SliceIndexRangeToUsizeSliceInst,
    quotientCut, bind_ok]
  dsimp! only
  simp only [factorsCopy, startCast, lengthCast, core.result.Result.expect,
    directionOk, stackCut, bind_ok]
  dsimp! only
  simp only [nonaffine, Bool.false_eq_true, ite_false, pendingOk,
    Slice.index_mut_SliceIndexRangeToUsizeSliceInst, modulusCut, bind_ok]
  dsimp! only
  simp only [modulusCopy, bind_ok, afterCall]
  let final : Roots := { roots with pending := pending, degree := roots.gcd_degree, direction := direction, checked := true, affine := false }
  change Aeneas.Std.bind (Roots.stage final) _ = _
  rw [ClosedLeafAdvance.stage_refines final, bind_ok]
  all_goals rfl

theorem commit_affine (exactDivision : ExactDivide) {F K : Type}
    (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (roots : Roots) (buffers : FactorWork) (factors : Slice U64) (stack : Slice FactorFrame)
    (meter paid finalMeter : WorkMeter) (length start stop pending rank baseSum baseIndex : Usize)
    (basis : Array U64 64#usize) (basisWord : U64)
    (startWord lengthWord : U64) (direction : U32) (quotient remainder : Slice U64) (raw : Slice RawProduct)
    (workRoom : roots.degree.val + 2 ≤ buffers.work.length)
    (gcdRoom : roots.gcd_len.val ≤ buffers.gcd.length)
    (charged : charge meter (.Divide roots.degree) = .ok (.Ok (), paid))
    (call : reached exactDivision field kernels roots buffers (some length) quotient remainder raw)
    (assembly : charge paid (.SplitAssembly roots.degree) = .ok (.Ok (), finalMeter))
    (startOk : Usize.checked_mul roots.pending roots.stride = some start)
    (endOk : Usize.checked_add start length = some stop)
    (endpoint : stop.val = start.val + length.val) (factorRoom : stop.val ≤ factors.length)
    (quotientRoom : length.val ≤ quotient.length) (slotRoom : roots.pending.val < stack.length)
    (modulusRoom : roots.gcd_len.val ≤ buffers.modulus.length)
    (startCast : U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from start = .ok (.Ok startWord))
    (lengthCast : U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from length = .ok (.Ok lengthWord))
    (directionOk : (roots.direction + 1#u32 : Result U32) = .ok direction)
    (pendingOk : (roots.pending + 1#usize : Result Usize) = .ok pending)
    (affine : roots.affine = true)
    (rankOk : (roots.affine_rank - 1#usize : Result Usize) = .ok rank)
    (basisPresent : buffers.basis.directions = some basis)
    (basisRead : Array.index_usize basis rank = .ok basisWord)
    (sumOk : (start + roots.stride : Result Usize) = .ok baseSum)
    (indexOk : (baseSum - 1#usize : Result Usize) = .ok baseIndex)
    (baseRoom : baseIndex.val < factors.length) :
    let updated := { roots with pending := pending, degree := roots.gcd_degree, direction := direction, checked := true, affine_rank := rank }
    let buffers' := { afterCall roots buffers quotient remainder raw with
      modulus := restorePrefix buffers.modulus (prefixSlice buffers.gcd roots.gcd_len.val) }
    let factors' := (factors.setSlice! start.val (prefixSlice quotient length.val).val).set baseIndex
      (roots.affine_base ^^^ basisWord)
    let frame : FactorFrame := ⟨startWord, lengthWord, direction, 1#u32⟩
    Roots.divide exactDivision field kernels roots buffers factors stack meter =
      .ok (.Ok (.Ok (ClosedLeafAdvance.stageFor updated)), updated, buffers', id,
        factors', (stack.set roots.pending frame).set roots.pending
          { frame with next_direction := UScalar.cast .U32 rank }, finalMeter) := by
  obtain ⟨width, added, split, divisor⟩ := call_prelude roots buffers workRoom gcdRoom
  have factorCut := ClosedLeaf.mutable_region_normal factors start stop (by omega) factorRoom
  have quotientCut := shared_prefix_normal quotient length quotientRoom
  have factorsCopy := ClosedLeaf.copy_normal
    (ClosedLeaf.region factors start.val stop.val) (prefixSlice quotient length.val) (by
      rw [ClosedLeaf.region_length _ _ _ factorRoom, prefix_length, Nat.min_eq_left quotientRoom, endpoint]
      omega)
  have modulusCut := prefix_normal buffers.modulus roots.gcd_len modulusRoom
  have modulusCopy := ClosedLeaf.copy_normal
    (prefixSlice buffers.modulus roots.gcd_len.val) (prefixSlice buffers.gcd roots.gcd_len.val) (by
      rw [prefix_length, Nat.min_eq_left modulusRoom, prefix_length, Nat.min_eq_left gcdRoom])
  obtain ⟨⟨old, back⟩, stackCut, _, backExact⟩ := RawMulTable.normal_of_spec _ _
    (Slice.index_mut_usize_spec stack roots.pending slotRoom)
  rw [backExact] at stackCut
  let firstFrame : FactorFrame := ⟨startWord, lengthWord, direction, 1#u32⟩
  let firstStack := stack.set roots.pending firstFrame
  have againRoom : roots.pending.val < firstStack.length := by
    unfold firstStack
    rwa [Slice.set_length]
  obtain ⟨⟨oldAgain, backAgain⟩, againCut, frameValue, againBack⟩ := RawMulTable.normal_of_spec _ _
    (Slice.index_mut_usize_spec firstStack roots.pending againRoom)
  have sameFrame : oldAgain = firstFrame := by
    rw [frameValue]
    have inBounds : roots.pending.val < (stack.val.set roots.pending.val firstFrame).length := by
      rw [List.length_set]
      exact slotRoom
    simp only [firstStack, Slice.set, Slice.setAtNat, Slice.from_val]
    exact List.getElem_set_self inBounds
  rw [sameFrame, againBack] at againCut
  have wroteBase := Reconstruction.update_normal
    (factors.setSlice! start.val (prefixSlice quotient length.val).val) baseIndex
    (roots.affine_base ^^^ basisWord) (by rwa [Slice.setSlice!_length])
  simp only [Roots.divide, charged, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  dsimp! only
  simp only [added, split, bind_ok]
  dsimp! only
  simp only [divisor, bind_ok, reached] at call ⊢
  rw [call]
  simp only [bind_ok, assembly, core.result.Result.Insts.CoreOpsTry.branch]
  dsimp! only
  simp only [lift, bind_ok, startOk, endOk, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch]
  simp only [core.slice.index.Slice.index_mut, factorCut, Slice.index_SliceIndexRangeToUsizeSliceInst,
    quotientCut, bind_ok]
  dsimp! only
  simp only [factorsCopy, startCast, lengthCast, core.result.Result.expect,
    directionOk, stackCut, bind_ok]
  dsimp! only
  simp only [affine, ite_true, rankOk, sharedOption, basisPresent, core.option.Option.expect,
    Result.ofOption, basisRead, sumOk, indexOk, lift, bind_ok]
  simp only [firstStack, firstFrame] at againCut
  simp only [wroteBase, againCut, bind_ok]
  try dsimp! only
  simp only [lift, bind_ok, pendingOk, Slice.index_mut_SliceIndexRangeToUsizeSliceInst, modulusCut]
  dsimp! only
  simp only [modulusCopy, bind_ok, afterCall]
  let final : Roots := { roots with pending := pending, degree := roots.gcd_degree, direction := direction, checked := true, affine := true, affine_rank := rank }
  change Aeneas.Std.bind (Roots.stage final) _ = _
  rw [ClosedLeafAdvance.stage_refines final, bind_ok]
  all_goals rfl



end BulksketchBridge.RootDivide
