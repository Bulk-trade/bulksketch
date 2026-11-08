import BulksketchBridge.BmTerminalSpec
import BulksketchBridge.BmMutableFrames
import BulksketchBridge.InverseUsing
import BulksketchBridge.RebuiltLocatorLoop

namespace BulksketchBridge.BmTerminal

open Aeneas Aeneas.Std Aeneas.Std.WP DenseCoefficient RebuiltLfsr
open bulksketch.backend.contract bulksketch.decode.bm bulksketch.types

set_option maxRecDepth 4096

private theorem read_normal (words : Slice U64) (index : Usize) (bounded : index.val < words.length) :
    Slice.index_usize words index = Result.ok words[index.val]! := by
  obtain ⟨word, normal, exactWord⟩ := RawMulTable.normal_of_spec _ _
    (Slice.index_usize_spec words index bounded)
  rw [normal, exactWord, Slice.getElem!_Nat_eq]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! _ _ bounded)

private theorem mutable_prefix (words : Slice U64) (last : Usize) (bound : last.val < words.length) :
    core.slice.index.Slice.index_mut (RebuiltLfsrRuntime.inclusive U64) words ⟨last⟩ =
      Result.ok (prefixSlice words (last.val + 1), restorePrefix words) := by
  have sizeBound : words.length ≤ Usize.max := words.length_ineq
  obtain ⟨stop, addNormal, addValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := last) (y := 1#usize) (by change last.val + 1 ≤ Usize.max; omega))
  have exactStop : stop.val = last.val + 1 := addValue
  have sliced := prefix_normal words stop (by omega)
  change (RebuiltLfsrRuntime.inclusive U64).index_mut ⟨last⟩ words = _
  simp only [RebuiltLfsrRuntime.inclusive, bound, ite_true, addNormal, bind_ok, sliced, exactStop]

private theorem scaled_length (connection : Slice U64) (degree : Nat) (scale : U64) :
    (scaledPrefix connection degree scale).length = (prefixSlice connection (degree + 1)).length := by
  simp [scaledPrefix, prefixSlice, Slice.length]

private theorem patch_scaled (connection : Slice U64) (degree : Nat) (scale : U64) :
    let coefficients := prefixSlice connection (degree + 1)
    BmMutable.patchWords (fun index => mulWord coefficients[index]! scale) 0 coefficients.length coefficients =
      scaledPrefix connection degree scale := by
  let coefficients := prefixSlice connection (degree + 1)
  let scaled := scaledPrefix connection degree scale
  have scaleVal : scaled.val = coefficients.val.map (fun word => mulWord word scale) := by
    simp only [scaled, scaledPrefix, coefficients, prefixSlice, Slice.from_val]
  have scaleLen : scaled.length = coefficients.length := scaled_length connection degree scale
  let patched := BmMutable.patchWords (fun index => mulWord coefficients[index]! scale)
    0 coefficients.length coefficients
  have patchLen : patched.length = coefficients.length := BmMutable.patchWords_length _ _ _ _
  change patched = scaled
  apply Slice.ext
  apply List.ext_getElem (patchLen.trans scaleLen.symm)
  intro index leftBound rightBound
  have bounded : index < coefficients.length := by change index < patched.length at leftBound; omega
  rw [List.Inhabited_getElem_eq_getElem! _ _ leftBound, List.getElem_of_eq scaleVal, List.getElem_map]
  rw [← Slice.getElem!_Nat_eq]
  change (BmMutable.patchWords _ 0 coefficients.length coefficients)[index]! = _
  rw [BmMutable.patchWords_word _ _ _ _ _ bounded]
  simp only [Nat.zero_le, Nat.zero_add, bounded, and_self, ite_true, Slice.getElem!_Nat_eq]
  rw [List.Inhabited_getElem_eq_getElem! _ _ bounded]

private theorem prefix_restored (connection replacement : Slice U64)
    (room : replacement.length ≤ connection.length) :
    prefixSlice (restorePrefix connection replacement) replacement.length = replacement := by
  apply Slice.ext
  have fits : replacement.val.length ≤ connection.val.length := room
  simp only [prefixSlice, restorePrefix, Slice.from_val, List.setSlice!, Nat.sub_zero, Nat.zero_add,
    List.take_zero, List.nil_append, Nat.min_eq_left fits, List.take_length]
  change (replacement.val ++ connection.val.drop replacement.val.length).take replacement.val.length = replacement.val
  rw [List.take_left]

private theorem restore_twice (connection replacement final : Slice U64)
    (same : final.length = replacement.length) (room : replacement.length ≤ connection.length) :
    restorePrefix (restorePrefix connection replacement) final = restorePrefix connection final := by
  apply Slice.ext
  have fits : replacement.val.length ≤ connection.val.length := room
  have finalLen : final.val.length = replacement.val.length := same
  have joinedLen : (replacement.val ++ connection.val.drop replacement.val.length).length =
      connection.val.length := by
    simp only [List.length_append, List.length_drop]
    omega
  simp only [restorePrefix, Slice.from_val, List.setSlice!, Nat.sub_zero, Nat.zero_add,
    List.take_zero, List.nil_append, finalLen, joinedLen, Nat.min_eq_left fits, List.take_length]
  have takeFinal : final.val.take replacement.val.length = final.val := by rw [← finalLen, List.take_length]
  rw [takeFinal, List.drop_left]

private theorem inverse_normal {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : NativeInverse kernels) (word : U64) (nonzero : word ≠ 0#u64) :
    kernels.ArithmeticInst.inverse word = .ok (some (inverseWord word)) := by
  rw [arithmetic, InverseUsing.inverse_refines]
  simp only [Inverse.expectedFieldInverse, ite_eq_right nonzero, DirectTwo.inverseWord]

theorem body_refines : ActualBmTerminalBody := by
  intro K kernels mul inverse back0 back1 back2 tail syndromes budget cost iter meter
    connection previous saved degree previousLen shift previousDelta exhausted degreeBound
  obtain ⟨⟨option, next⟩, nextNormal, noneEq, sameIter⟩ := RawMulTable.normal_of_spec _ _
    (core.iter.range.IteratorRange.next_Usize_none_spec iter exhausted)
  rw [noneEq, sameIter] at nextNormal
  have leading := read_normal connection degree degreeBound
  have constant := read_normal connection 0#usize (by change 0 < connection.length; omega)
  change Slice.index_usize connection 0#usize = Result.ok connection[0]! at constant
  simp only [locator_loop0.body, nextNormal, leading, bind_ok]
  dsimp! only
  by_cases leadZero : connection[degree.val]! = 0#u64
  · simp only [leadZero, ite_true, terminalResult, true_or, joinBuffers]
  · by_cases constantZero : connection[0]! = 0#u64
    · simp only [leadZero, ite_false, constant, bind_ok, constantZero, ite_true,
        terminalResult, or_true, joinBuffers]
    · let scale := inverseWord connection[0]!
      let coefficients := prefixSlice connection (degree.val + 1)
      let scaled := scaledPrefix connection degree.val scale
      let connection1 := restorePrefix connection scaled
      have prefixNormal := mutable_prefix connection degree degreeBound
      change _ = Result.ok (coefficients, restorePrefix connection) at prefixNormal
      have coeffLen : coefficients.length = degree.val + 1 := by
        simp only [coefficients, prefix_length, Nat.min_eq_left (by omega : degree.val + 1 ≤ connection.length)]
      have scaledLen : scaled.length = degree.val + 1 := (scaled_length _ _ _).trans coeffLen
      have normalization : locator_loop0_loop0 fieldDictionary kernels ⟨coefficients, 0⟩ (fun state => state) scale =
          Result.ok (BmMutable.iterResult coefficients (fun word => mulWord word scale) 0 id) :=
        BmMutable.normalize_loop_refines kernels mul coefficients 0 id scale (Nat.zero_le _)
      have invNormal : kernels.ArithmeticInst.inverse connection[0]! = Result.ok (some scale) :=
        inverse_normal kernels inverse _ constantZero
      have patch : BmMutable.patchWords (fun index => mulWord coefficients[index]! scale)
          0 coefficients.length coefficients = scaled := patch_scaled connection degree.val scale
      have scaledPayload : ((BmMutable.iterResult coefficients (fun word => mulWord word scale) 0 id).2
          (BmMutable.iterResult coefficients (fun word => mulWord word scale) 0 id).1).slice = scaled := by
        simp only [BmMutable.iterResult, Nat.sub_zero, id_eq, BmMutable.iter_writeback, patch]
      have connLen : connection1.length = connection.length := restore_length _ _
      have nextPrefix := mutable_prefix connection1 degree (by omega)
      have samePrefix : prefixSlice connection1 (degree.val + 1) = scaled := by
        rw [← scaledLen]
        exact prefix_restored connection scaled (by omega)
      rw [samePrefix] at nextPrefix
      have reverseLen : (core.slice.Slice.reverse scaled).length = scaled.length := by
        simp [core.slice.Slice.reverse, Slice.length]
      have final : restorePrefix connection1 (core.slice.Slice.reverse scaled) =
          normalizedConnection connection degree.val := by
        rw [show connection1 = restorePrefix connection scaled from rfl,
          restore_twice _ _ _ reverseLen (by omega)]
        rfl
      simp only [leadZero, ite_false, constant, bind_ok, constantZero, invNormal,
        core.option.Option.expect, prefixNormal]
      dsimp! only
      simp only [core.slice.Slice.iter_mut, bind_ok]
      dsimp! only
      simp only [normalization, bind_ok]
      dsimp! only
      simp only [scaledPayload, show restorePrefix connection scaled = connection1 from rfl,
        nextPrefix, bind_ok]
      dsimp! only
      simp only [lift, bind_ok, final, terminalResult, leadZero, constantZero, or_self, ite_false, joinBuffers]

theorem loop_refines : ActualBmTerminalLoop := by
  intro K kernels mul inverse back0 back1 back2 tail syndromes budget cost iter meter
    connection previous saved degree previousLen shift previousDelta exhausted degreeBound
  have body := body_refines kernels mul inverse back0 back1 back2 tail syndromes budget cost iter meter
    connection previous saved degree previousLen shift previousDelta exhausted degreeBound
  unfold locator_loop0 loop
  dsimp only
  simp only [body, bind_ok]

end BulksketchBridge.BmTerminal
