import BulksketchBridge.X86PclmulSliceChallenges
import BulksketchBridge.X86PclmulMaps
import BulksketchBridge.Algebra.WordLaws

namespace BulksketchBridge.X86PclmulSlice

open Aeneas Aeneas.Std Aeneas.Std.X86PclmulRuntime
open BulksketchBridge.MutableZip BulksketchBridge.Algebra.Gf64 X86PclmulSliceChallenges
open bulksketch.backend.x86_pclmul

private theorem length_check (dst src : Slice U64) :
    Slice.len dst = Slice.len src ↔ dst.length = src.length := by
  constructor
  · intro same
    simpa using congrArg UScalar.val same
  · intro same
    exact UScalar.eq_of_val_eq (by simpa using same)

private theorem scale_zero (left right : U64) : scaledWord 0#u64 left right = left := by
  apply U64.bv_eq_imp_eq
  change left.bv ^^^ multiplyWord right.bv 0 = left.bv
  rw [multiplyWord_zero]
  simp

private theorem scale_one (left right : U64) :
    scaledWord 1#u64 left right = left ^^^ right := by
  apply U64.bv_eq_imp_eq
  change left.bv ^^^ multiplyWord right.bv 1 = left.bv ^^^ right.bv
  rw [multiplyWord_one]

private theorem scale_zero_frame (dst src : Slice U64) :
    mapPrefixFrom dst src (scaledWord 0#u64) 0 = dst := by
  apply Slice.ext_getElem (by simp)
  intro index mappedBound bound
  rw [Slice.Inhabited_getElem_eq_getElem! _ index mappedBound,
    Slice.Inhabited_getElem_eq_getElem! dst index bound,
    mapPrefixFrom_word dst src _ 0 index bound]
  simp only [scale_zero, ite_self]

private theorem xor_step (dst src : Slice U64) (index : Nat)
    (active : index < min dst.length src.length) (back : State U64 U64 → State U64 U64) :
    scale_xor_loop0.body (stateAt dst src index) back =
      Result.ok (ControlFlow.cont (stateAt dst src (index + 1),
        fun final => back (replaceLeft final index (dst[index]! ^^^ src[index]!)))) := by
  have leftBound : index < dst.length := by omega
  have rightBound : index < src.length := by omega
  simp only [scale_xor_loop0.body, next_some_at dst src index leftBound rightBound, bind_ok, lift]
  dsimp! only
  rw [Slice.Inhabited_getElem_eq_getElem! dst index leftBound,
    Slice.Inhabited_getElem_eq_getElem! src index rightBound]

private theorem xor_done (dst src : Slice U64) (back : State U64 U64 → State U64 U64) :
    scale_xor_loop0.body (stateAt dst src (min dst.length src.length)) back =
      Result.ok (ControlFlow.done (back (stateAt dst src (min dst.length src.length)))) := by
  rw [scale_xor_loop0.body, next_done_at dst src _ (by omega), bind_ok]
  rfl

private theorem scaled_product (cl : Bool) (source scale : U64) :
    (do
      let input ← word source
      let product ← clmul 0#i32 input (scale.bv.setWidth 128)
      let reduced ← reduced cl dictionary product
      low reduced) =
        Result.ok (⟨multiplyWord source.bv scale.bv⟩ : U64) := by
  have same :
      multiply cl dictionary source scale =
        (do
          let input ← word source
          let product ← clmul 0#i32 input (scale.bv.setWidth 128)
          let reduced ← reduced cl dictionary product
          low reduced) := by
    simp only [multiply, X86Pclmul.word_refines scale, bind_ok]
  rw [← same]
  exact X86Pclmul.multiply_refines cl source scale

theorem scale_xor_refines : ScaleRefines := by
  intro cl dst src scale
  unfold scale_xor
  split
  · rename_i zero
    subst scale
    rw [scale_zero_frame]
  · split
    · rename_i one
      subst scale
      have asXor : scaledWord 1#u64 = (fun left right : U64 => left ^^^ right) := by
        funext left right
        exact scale_one left right
      rw [asXor]
      exact run_prefix_map dst src (· ^^^ ·)
        (fun pair => scale_xor_loop0.body pair.1 pair.2)
        (xor_step dst src) (xor_done dst src)
    · rw [X86Pclmul.word_refines scale, bind_ok]
      apply run_prefix_map dst src (scaledWord scale)
        (fun pair => scale_xor_loop1.body cl dictionary (scale.bv.setWidth 128) pair.1 pair.2)
      · intro index active back
        have leftBound : index < dst.length := by omega
        have rightBound : index < src.length := by omega
        change scale_xor_loop1.body cl dictionary (scale.bv.setWidth 128)
          (stateAt dst src index) back = _
        simp only [scale_xor_loop1.body, next_some_at dst src index leftBound rightBound, bind_ok]
        dsimp! only
        rw [Slice.Inhabited_getElem_eq_getElem! dst index leftBound,
          Slice.Inhabited_getElem_eq_getElem! src index rightBound]
        trans (do
          let product ← (do
            let input ← word src[index]!
            let product ← clmul 0#i32 input (scale.bv.setWidth 128)
            let reduced ← reduced cl dictionary product
            low reduced)
          let target ← lift (dst[index]! ^^^ product)
          Result.ok (ControlFlow.cont (stateAt dst src (index + 1),
            fun final => back (replaceLeft final index target))))
        · simp only [Aeneas.Std.bind_assoc]
        · rw [scaled_product]
          simp only [bind_ok, lift]
          rfl
      · intro back
        change scale_xor_loop1.body cl dictionary (scale.bv.setWidth 128)
          (stateAt dst src (min dst.length src.length)) back = _
        rw [scale_xor_loop1.body, next_done_at dst src _ (by omega), bind_ok]
        rfl

theorem square_slice_refines : SquareRefines := by
  intro cl dst src
  unfold square_slice
  apply run_prefix_map dst src (fun _ source => Square.expectedWord source)
    (fun pair => square_slice_loop.body cl dictionary pair.1 pair.2)
  · intro index active back
    have leftBound : index < dst.length := by omega
    have rightBound : index < src.length := by omega
    change square_slice_loop.body cl dictionary (stateAt dst src index) back = _
    simp only [square_slice_loop.body, next_some_at dst src index leftBound rightBound, bind_ok]
    dsimp! only
    rw [Slice.Inhabited_getElem_eq_getElem! src index rightBound]
    trans (do
      let target ← multiply cl dictionary src[index]! src[index]!
      Result.ok (ControlFlow.cont (stateAt dst src (index + 1),
        fun final => back (replaceLeft final index target))))
    · simp only [multiply, X86Pclmul.word_refines src[index]!, bind_ok,
        Aeneas.Std.bind_assoc]
    · rw [X86PclmulMaps.multiply_square_refines]
      exact bind_ok _ _
  · intro back
    change square_slice_loop.body cl dictionary (stateAt dst src (min dst.length src.length)) back = _
    rw [square_slice_loop.body, next_done_at dst src _ (by omega), bind_ok]
    rfl

theorem scale_xor_entry_refines : ScaleEntryRefines := by
  intro dst src scale
  unfold bulksketch.backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.scale_xor
  simp only [length_check]
  split
  · exact scale_xor_refines true dst src scale
  · simp only [core.fmt.Arguments.from_str]
    exact bind_ok (() : core.fmt.Arguments) (fun _ => Result.fail Error.panic)

theorem square_slice_entry_refines : SquareEntryRefines := by
  intro dst src
  unfold bulksketch.backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.square_slice
  simp only [length_check]
  split
  · exact square_slice_refines true dst src
  · simp only [core.fmt.Arguments.from_str]
    exact bind_ok (() : core.fmt.Arguments) (fun _ => Result.fail Error.panic)

theorem xor_assign_refines : XorEntryRefines := by
  intro dst src
  unfold bulksketch.backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels.xor_assign
  simp only [length_check]
  split
  · exact run_prefix_map dst src (· ^^^ ·)
      (fun pair => scale_xor_loop0.body pair.1 pair.2)
      (xor_step dst src) (xor_done dst src)
  · simp only [core.fmt.Arguments.from_str]
    exact bind_ok (() : core.fmt.Arguments) (fun _ => Result.fail Error.panic)

end BulksketchBridge.X86PclmulSlice
