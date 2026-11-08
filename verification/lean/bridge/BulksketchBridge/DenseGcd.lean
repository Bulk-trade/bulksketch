import BulksketchBridge.DenseGcdSpec
import BulksketchBridge.BmEntry
import BulksketchBridge.InverseUsing
import BulksketchBridge.ClosedLeafAdvance

namespace BulksketchBridge.DenseGcd

open Aeneas Aeneas.Std DenseCoefficient RebuiltLfsr BmEntry
open bulksketch.backend.contract bulksketch.types
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem Ready.leftLength {width : Nat} {state : State} (ready : Ready width state) :
    state.leftWords.length = state.leftLen.val := by
  unfold State.leftWords
  rw [prefix_length, Nat.min_eq_left (ready.leftRoom.le.trans (by rw [ready.leftWidth]))]

theorem Ready.rightLength {width : Nat} {state : State} (ready : Ready width state) :
    state.rightWords.length = state.rightLen.val := by
  unfold State.rightWords
  rw [prefix_length, Nat.min_eq_left (ready.rightRoom.le.trans (by rw [ready.rightWidth]))]

theorem Ready.advance {width : Nat} {state : State} (ready : Ready width state)
    (qLen remLen : Usize) (qOut remOut : Slice U64) (rawOut : Slice RawProduct)
    (qWidth : qOut.length = state.quotient.length) (remWidth : remOut.length = state.remainder.length)
    (rawWidth : rawOut.length = state.raw.length) (decrease : remLen.val < state.rightWords.length)
    (normalized : Normal (prefixSlice remOut remLen.val)) :
    Ready width (state.advance ((qLen, remLen), qOut, remOut, rawOut)) := by
  rw [ready.rightLength] at decrease
  exact ⟨ready.rightWidth, remWidth.trans ready.remainderWidth, qWidth.trans ready.quotientWidth,
    ready.leftWidth, rawWidth ▸ ready.rawRoom, ready.rightRoom,
    decrease.trans ready.rightRoom, ready.rightNormal, normalized⟩

theorem native_body_stop (division : DivRem) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (state : State) (zero : state.rightLen = 0#usize) :
    monic_gcd_into_loop.body division dictionary kernels state.back state.raw state.left state.right
      state.quotient state.remainder state.leftLen state.rightLen = .ok (.done state.finish) := by
  simp only [monic_gcd_into_loop.body, zero, bne_self_eq_false, Bool.false_eq_true, ite_false, State.finish]

theorem native_body_advance (division : DivRem) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (width : Nat) (state : State) (ready : Ready width state) (positive : state.rightLen ≠ 0#usize)
    (qLen remLen : Usize) (qOut remOut : Slice U64) (rawOut : Slice RawProduct)
    (call : division dictionary kernels state.leftWords state.rightWords state.quotient state.remainder state.raw =
      .ok ((qLen, remLen), qOut, remOut, rawOut)) :
    let next := state.advance ((qLen, remLen), qOut, remOut, rawOut)
    monic_gcd_into_loop.body division dictionary kernels state.back state.raw state.left state.right
      state.quotient state.remainder state.leftLen state.rightLen =
      .ok (.cont (next.back, next.raw, next.left, next.right, next.quotient, next.remainder,
        next.leftLen, next.rightLen)) := by
  have test : (state.rightLen != 0#usize) = true := by simp [positive]
  have left := shared_prefix_normal state.left state.leftLen
    (ready.leftRoom.le.trans (by rw [ready.leftWidth]))
  have right := shared_prefix_normal state.right state.rightLen
    (ready.rightRoom.le.trans (by rw [ready.rightWidth]))
  simp only [monic_gcd_into_loop.body, test, ite_true, Slice.index_SliceIndexRangeToUsizeSliceInst,
    left, right, bind_ok]
  change Std.bind (division dictionary kernels state.leftWords state.rightWords
    state.quotient state.remainder state.raw) _ = _
  rw [call, bind_ok]
  rfl

theorem run_refines (division : DivRem) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (law : DivisionLaw division kernels) (width fuel : Nat) (state : State)
    (ready : Ready width state) (enough : state.rightLen.val ≤ fuel) :
    ∃ final, run division kernels fuel state = .ok final ∧
      monic_gcd_into_loop division dictionary kernels state.back state.raw state.left state.right
        state.quotient state.remainder state.leftLen state.rightLen = .ok final.finish ∧
      Ready width final ∧ final.rightLen = 0#usize := by
  induction fuel generalizing state with
  | zero =>
    have zero : state.rightLen = 0#usize := by
      apply UScalar.eq_of_val_eq
      simpa using enough
    refine ⟨state, by simp only [run, zero, ite_true], ?_, ready, zero⟩
    unfold monic_gcd_into_loop
    rw [loop]
    dsimp only
    rw [native_body_stop division kernels state zero, bind_ok]
  | succ fuel ih =>
    by_cases zero : state.rightLen = 0#usize
    · refine ⟨state, by simp only [run, zero, ite_true], ?_, ready, zero⟩
      unfold monic_gcd_into_loop
      rw [loop]
      dsimp only
      rw [native_body_stop division kernels state zero, bind_ok]
    · have nonzero : 0 < state.rightLen.val := by
        apply Nat.pos_of_ne_zero
        intro h
        apply zero
        apply UScalar.eq_of_val_eq
        simpa using h
      obtain ⟨qLen, remLen, qOut, remOut, rawOut, call, qWidth, remWidth, rawWidth, decrease, normalized⟩ :=
        law state.leftWords state.rightWords state.quotient state.remainder state.raw
          ready.leftNormal ready.rightNormal (ready.rightLength.symm ▸ nonzero)
          (by rw [ready.leftLength, ready.quotientWidth]; exact ready.leftRoom)
          (by rw [ready.leftLength, ready.remainderWidth]; exact ready.leftRoom)
          (by rw [ready.leftLength]; exact ready.leftRoom.trans_le ready.rawRoom)
      let next := state.advance ((qLen, remLen), qOut, remOut, rawOut)
      have nextReady := ready.advance qLen remLen qOut remOut rawOut qWidth remWidth rawWidth decrease normalized
      have nextFuel : next.rightLen.val ≤ fuel := by
        rw [ready.rightLength] at decrease
        change remLen.val ≤ fuel
        omega
      obtain ⟨final, modeled, native, finalReady, finalZero⟩ := ih next nextReady nextFuel
      refine ⟨final, ?_, ?_, finalReady, finalZero⟩
      · simp only [run, zero, ite_false, call, bind_ok]
        exact modeled
      · unfold monic_gcd_into_loop
        rw [loop]
        dsimp only
        rw [native_body_advance division kernels width state ready zero qLen remLen qOut remOut rawOut call, bind_ok]
        exact native

theorem prefix_restored (words replacement : Slice U64) (room : replacement.length ≤ words.length) :
    prefixSlice (restorePrefix words replacement) replacement.length = replacement := by
  apply Slice.ext
  have fits : replacement.val.length ≤ words.val.length := room
  simp only [prefixSlice, restorePrefix, Slice.from_val, List.setSlice!, Nat.sub_zero, Nat.zero_add,
    List.take_zero, List.nil_append, Nat.min_eq_left fits, List.take_length]
  change (replacement.val ++ words.val.drop replacement.val.length).take replacement.val.length = replacement.val
  rw [List.take_left]

private theorem zero_length (words : Slice U64) : (zeroWords words).length = words.length := by
  simp only [zeroWords, Slice.length, Slice.from_val, List.length_replicate]

theorem start_left (a b work : Slice U64) (raw : Slice RawProduct)
    (width : Nat) (workRoom : 4 * width ≤ work.length) (room : a.length < width) :
    (startState width a b work raw).leftWords = a := by
  let front := prefixSlice work (4 * width)
  have frontLen : front.length = 4 * width := by
    simp only [front, prefix_length, Nat.min_eq_left workRoom]
  have leftWidth : (prefixSlice front width).length = width := by
    rw [prefix_length, Nat.min_eq_left (by omega)]
  simpa only [State.leftWords, startState, Slice.len_val] using
    prefix_restored (prefixSlice front width) a (by rw [leftWidth]; omega)

theorem start_right (a b work : Slice U64) (raw : Slice RawProduct)
    (width : Nat) (workRoom : 4 * width ≤ work.length) (room : b.length < width) :
    (startState width a b work raw).rightWords = b := by
  let front := prefixSlice work (4 * width)
  have frontLen : front.length = 4 * width := by
    simp only [front, prefix_length, Nat.min_eq_left workRoom]
  let rest := tail front width
  have restLen : rest.length = 4 * width - width := by dsimp only [rest]; rw [tail_length, frontLen]
  have rightWidth : (prefixSlice rest width).length = width := by
    rw [prefix_length, Nat.min_eq_left (by omega)]
  simpa only [State.rightWords, startState, Slice.len_val] using
    prefix_restored (prefixSlice rest width) b (by rw [rightWidth]; omega)

theorem start_ready (a b work : Slice U64) (raw : Slice RawProduct) (width : Nat)
    (workRoom : 4 * width ≤ work.length) (rawRoom : width ≤ raw.length)
    (aRoom : a.length < width) (bRoom : b.length < width)
    (aNormal : Normal a) (bNormal : Normal b) :
    Ready width (startState width a b work raw) := by
  let front := prefixSlice work (4 * width)
  let rest := tail front width
  let rest1 := tail rest width
  have frontLen : front.length = 4 * width := by dsimp only [front]; rw [prefix_length, Nat.min_eq_left workRoom]
  have restLen : rest.length = 3 * width := by dsimp only [rest]; rw [tail_length, frontLen]; omega
  have rest1Len : rest1.length = 2 * width := by dsimp only [rest1]; rw [tail_length, restLen]; omega
  have firstWidth : (prefixSlice front width).length = width := by rw [prefix_length, Nat.min_eq_left (by omega)]
  have secondWidth : (prefixSlice rest width).length = width := by rw [prefix_length, Nat.min_eq_left (by omega)]
  have thirdWidth : (prefixSlice rest1 width).length = width := by rw [prefix_length, Nat.min_eq_left (by omega)]
  have fourthWidth : (tail rest1 width).length = width := by rw [tail_length, rest1Len]; omega
  refine ⟨?_, ?_, thirdWidth, fourthWidth, rawRoom, ?_, ?_, ?_, ?_⟩
  · exact (restore_length _ _).trans firstWidth
  · exact (restore_length _ _).trans secondWidth
  · simpa only [startState, Slice.len_val] using aRoom
  · simpa only [startState, Slice.len_val] using bRoom
  · rwa [start_left a b work raw width workRoom aRoom]
  · rwa [start_right a b work raw width workRoom bRoom]

private theorem zeroed_word (dst : Slice U64) (limit index : Nat)
    (room : limit ≤ dst.length) (bound : index < limit) :
    (restorePrefix dst (zeroWords (prefixSlice dst limit)))[index]! = 0#u64 := by
  have len : (zeroWords (prefixSlice dst limit)).length = limit := by
    rw [zero_length, prefix_length, Nat.min_eq_left room]
  simp only [restorePrefix, Slice.getElem!_Nat_eq, Slice.from_val]
  rw [List.getElem!_setSlice!_middle _ _ _ _ (by change 0 ≤ index ∧ index - 0 <
    (zeroWords (prefixSlice dst limit)).length ∧ index < dst.length; omega), Nat.sub_zero]
  simp only [zeroWords, Slice.from_val]
  rw [List.getElem!_replicate]
  have width : (prefixSlice dst limit).length = limit := by rw [prefix_length, Nat.min_eq_left room]
  simp only [width, bound]

private theorem prefix_word (words : Slice U64) (len index : Nat)
    (bound : len ≤ words.length) (inside : index < len) :
    (prefixSlice words len)[index]! = words[index]! := by
  simp only [prefixSlice, Slice.getElem!_Nat_eq, Slice.from_val]
  simpa only [List.slice, List.drop_zero, Nat.sub_zero, Nat.zero_add] using
    List.getElem!_slice 0 len index words.val ⟨bound, by omega⟩

private theorem scale_normal {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : TimesXMod.ExactScaleXor kernels) (dst src : Slice U64) (scale : U64)
    (same : dst.length = src.length) (zeros : ∀ i < dst.length, dst[i]! = 0#u64) :
    kernels.ArithmeticInst.scale_xor dst src scale = .ok (scaledPrefix src scale) := by
  obtain ⟨out, normal, outLen, values⟩ := arithmetic dst src scale same
  have expectedLen : (scaledPrefix src scale).length = src.length := by simp [scaledPrefix, Slice.length]
  have exactOut : out = scaledPrefix src scale := by
    apply Slice.ext_getElem (outLen.trans (same.trans expectedLen.symm))
    intro i outRoom expectedRoom
    have bound : i < dst.length := by rwa [outLen] at outRoom
    rw [Slice.Inhabited_getElem_eq_getElem! _ _ outRoom, values i bound, zeros i bound]
    have srcRoom : i < src.val.length := by rw [same] at bound; exact bound
    change (0#u64 ^^^ _) = (scaledPrefix src scale).val[i]
    simp only [scaledPrefix, Slice.from_val, List.getElem_map]
    rw [Slice.getElem!_Nat_eq, ← List.Inhabited_getElem_eq_getElem! _ _ srcRoom]
    apply U64.bv_eq_imp_eq
    exact BitVec.zero_xor
  rwa [exactOut] at normal

private theorem leading_normal {width : Nat} {state : State} (ready : Ready width state)
    (positive : 0 < state.leftLen.val) :
    state.left[state.leftLen.val - 1]! ≠ 0#u64 := by
  have normalized := ready.leftNormal (by rwa [ready.leftLength])
  rw [ready.leftLength, State.leftWords,
    prefix_word _ _ _ (ready.leftRoom.le.trans (by rw [ready.leftWidth])) (by omega)] at normalized
  exact normalized

theorem monic_gcd_refines : ActualMonicGcd := by
  intro division K kernels a b dst work raw law inverse arithmetic aNormal bNormal dstRoom workRoom rawRoom
  let limit := max a.length b.length
  let widthNat := limit + 1
  let maxLen := core.cmp.impls.OrdUsize.max (Slice.len a) (Slice.len b)
  have maxValue : maxLen.val = limit := by
    simp only [maxLen, limit, core.cmp.impls.OrdUsize.max_val, Slice.len_val]
  have workMax : work.length ≤ Usize.max := work.length_ineq
  have rawMax : raw.length ≤ Usize.max := raw.length_ineq
  change 4 * widthNat ≤ work.length at workRoom
  change 2 * widthNat ≤ raw.length at rawRoom
  obtain ⟨width, widthNormal, widthValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := maxLen) (y := 1#usize) (by
      change maxLen.val + 1 ≤ Usize.max
      rw [maxValue]
      change widthNat ≤ Usize.max
      omega))
  change width.val = maxLen.val + 1 at widthValue
  rw [maxValue] at widthValue
  change width.val = widthNat at widthValue
  obtain ⟨four, fourNormal, fourValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.mul_spec (x := 4#usize) (y := width) (by
      change 4 * width.val ≤ Usize.max
      rw [widthValue]
      omega))
  change four.val = 4 * width.val at fourValue
  rw [widthValue] at fourValue
  obtain ⟨two, twoNormal, twoValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.mul_spec (x := 2#usize) (y := width) (by
      change 2 * width.val ≤ Usize.max
      rw [widthValue]
      omega))
  change two.val = 2 * width.val at twoValue
  rw [widthValue] at twoValue
  have assertDst : maxLen ≤ Slice.len dst := by rw [UScalar.le_equiv, maxValue, Slice.len_val]; exact dstRoom
  have assertWork : four ≤ Slice.len work := by rw [UScalar.le_equiv, fourValue, Slice.len_val]; exact workRoom
  have assertRaw : two ≤ Slice.len raw := by rw [UScalar.le_equiv, twoValue, Slice.len_val]; exact rawRoom
  have cutWork := prefix_normal work four (by rwa [fourValue])
  rw [fourValue] at cutWork
  let front := prefixSlice work (4 * widthNat)
  let rest := tail front widthNat
  let rest1 := tail rest widthNat
  have frontLen : front.length = 4 * widthNat := by dsimp only [front]; rw [prefix_length, Nat.min_eq_left workRoom]
  have restLen : rest.length = 3 * widthNat := by dsimp only [rest]; rw [tail_length, frontLen]; omega
  have rest1Len : rest1.length = 2 * widthNat := by dsimp only [rest1]; rw [tail_length, restLen]; omega
  have firstSplit := split_refines front width (by omega)
  rw [widthValue] at firstSplit
  have secondSplit := split_refines rest width (by omega)
  rw [widthValue] at secondSplit
  have thirdSplit := split_refines rest1 width (by omega)
  rw [widthValue] at thirdSplit
  let left := prefixSlice front widthNat
  let right := prefixSlice rest widthNat
  have leftWidth : left.length = widthNat := by dsimp only [left]; rw [prefix_length, Nat.min_eq_left (by omega)]
  have rightWidth : right.length = widthNat := by dsimp only [right]; rw [prefix_length, Nat.min_eq_left (by omega)]
  have aRoom : a.length < widthNat := Nat.lt_succ_of_le (Nat.le_max_left _ _)
  have bRoom : b.length < widthNat := Nat.lt_succ_of_le (Nat.le_max_right _ _)
  have cutLeft := prefix_normal left (Slice.len a) (by rw [Slice.len_val, leftWidth]; omega)
  have cutRight := prefix_normal right (Slice.len b) (by rw [Slice.len_val, rightWidth]; omega)
  rw [Slice.len_val] at cutLeft cutRight
  have copyLeft := ClosedLeaf.copy_normal (prefixSlice left a.length) a
    (by rw [prefix_length, Nat.min_eq_left (by omega)])
  have copyRight := ClosedLeaf.copy_normal (prefixSlice right b.length) b
    (by rw [prefix_length, Nat.min_eq_left (by omega)])
  let state := startState widthNat a b work raw
  have ready := start_ready a b work raw widthNat workRoom (by omega) aRoom bRoom aNormal bNormal
  obtain ⟨final, modeled, native, finalReady, finalZero⟩ :=
    run_refines division kernels law widthNat b.length state ready (by simp only [state, startState, Slice.len_val, Nat.le_refl])
  let output : Output := (final.leftLen, destination dst limit final, restoreWork work widthNat final, final.raw)
  refine ⟨output, ?_, ?_⟩
  · have cutDst := prefix_normal dst maxLen (by rwa [maxValue])
    rw [maxValue] at cutDst
    dsimp only [maxLen] at widthNormal assertDst cutDst
    simp only [monic_gcd_into, lift, bind_ok, widthNormal, massert, assertDst, fourNormal, assertWork,
      twoNormal, assertRaw, ite_true, Slice.index_mut_SliceIndexRangeToUsizeSliceInst, cutWork]
    dsimp! only
    rw [firstSplit]
    simp only [bind_ok]
    dsimp! only
    rw [secondSplit]
    simp only [bind_ok]
    dsimp! only
    rw [thirdSplit]
    simp only [bind_ok]
    dsimp! only
    rw [cutLeft]
    simp only [bind_ok]
    dsimp! only
    rw [copyLeft, bind_ok, cutRight]
    simp only [bind_ok]
    dsimp! only
    rw [copyRight, bind_ok]
    change Std.bind (monic_gcd_into_loop division dictionary kernels state.back state.raw state.left state.right
      state.quotient state.remainder state.leftLen state.rightLen) _ = _
    rw [native, bind_ok]
    simp only [State.finish, cutDst]
    dsimp! only
    simp only [fill_zero, bind_ok]
    by_cases zero : final.leftLen = 0#usize
    · simp only [zero, bne_self_eq_false, Bool.false_eq_true, ite_false, destination, output, restoreWork, ite_true]
      rfl
    · have positive : 0 < final.leftLen.val := by
        apply Nat.pos_of_ne_zero
        intro h
        apply zero
        apply UScalar.eq_of_val_eq
        simpa using h
      have test : (final.leftLen != 0#usize) = true := by simp [zero]
      have leadingNZ := leading_normal finalReady positive
      obtain ⟨last, lastNormal, lastValue, _⟩ := RawMulTable.normal_of_spec _ _
        (Usize.sub_spec (x := final.leftLen) (y := 1#usize) (by change 1 ≤ final.leftLen.val; omega))
      change last.val = final.leftLen.val - 1 at lastValue
      have leftBound : last.val < final.left.length := by
        have leftRoom := finalReady.leftRoom
        have length := finalReady.leftWidth
        omega
      obtain ⟨word, read, exactWord⟩ := RawMulTable.normal_of_spec _ _
        (Slice.index_usize_spec final.left last leftBound)
      have wordExact : word = final.left[final.leftLen.val - 1]! := by
        rw [exactWord, Slice.getElem!_Nat_eq, ← lastValue]
        exact List.Inhabited_getElem_eq_getElem! _ _ leftBound
      let zeroed := restorePrefix dst (zeroWords (prefixSlice dst limit))
      have zeroedLen : zeroed.length = dst.length := restore_length _ _
      have active : final.leftLen.val ≤ limit := by have bound := finalReady.leftRoom; omega
      have zeroedRoom : final.leftLen.val ≤ zeroed.length := by rw [zeroedLen]; exact active.trans dstRoom
      have cutOut := prefix_normal zeroed final.leftLen zeroedRoom
      dsimp only [zeroed] at cutOut
      have shared := shared_prefix_normal final.left final.leftLen
        (finalReady.leftRoom.le.trans (by rw [finalReady.leftWidth]))
      have outLength : (prefixSlice zeroed final.leftLen.val).length = final.leftLen.val := by
        rw [prefix_length, Nat.min_eq_left zeroedRoom]
      simp only [test, ite_true, lastNormal, bind_ok, read, wordExact]
      by_cases one : final.left[final.leftLen.val - 1]! = 1#u64
      · have copy := ClosedLeaf.copy_normal (prefixSlice zeroed final.leftLen.val) final.leftWords
          (outLength.trans finalReady.leftLength.symm)
        simp only [one, ite_true, Slice.index_SliceIndexRangeToUsizeSliceInst, shared, bind_ok]
        dsimp! only
        rw [cutOut]
        simp only [bind_ok]
        dsimp! only
        simp only [State.leftWords, zeroed] at copy
        rw [copy, bind_ok]
        simp only [output, destination, zero, ite_false, gcdWords, one, ite_true, restoreWork]
        rfl
      · have inv : kernels.ArithmeticInst.inverse final.left[final.leftLen.val - 1]! =
            .ok (some (DirectTwo.inverseWord final.left[final.leftLen.val - 1]!)) := by
          rw [inverse, InverseUsing.inverse_refines]
          simp only [Inverse.expectedFieldInverse, ite_eq_right leadingNZ, DirectTwo.inverseWord]
        have scale := scale_normal kernels arithmetic (prefixSlice zeroed final.leftLen.val) final.leftWords
          (DirectTwo.inverseWord final.left[final.leftLen.val - 1]!) (outLength.trans finalReady.leftLength.symm)
          (by intro i inside
              rw [outLength] at inside
              rw [prefix_word zeroed _ _ zeroedRoom inside]
              exact zeroed_word dst limit i dstRoom (inside.trans_le active))
        simp only [one, ite_false, inv, core.option.Option.expect, bind_ok,
          Slice.index_SliceIndexRangeToUsizeSliceInst, shared]
        dsimp! only
        simp only [bind_ok, cutOut]
        dsimp! only
        simp only [State.leftWords, zeroed] at scale
        rw [scale, bind_ok]
        simp only [output, destination, zero, ite_false, gcdWords, one, restoreWork]
        rfl
  · simp only [expected, limit, widthNat, state] at modeled ⊢
    rw [modeled, bind_ok]

end BulksketchBridge.DenseGcd
