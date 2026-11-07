import BulksketchBridge.PortableSliceChallenges
import BulksketchBridge.PortableXor
import BulksketchBridge.Algebra.WordNative
import BulksketchBridge.Algebra.WordLaws

namespace BulksketchBridge.PortableSlice

open Aeneas Aeneas.Std BulksketchBridge.MutableZip BulksketchBridge.Algebra.Gf64
open bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractArithmetic

private abbrev dictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField

private theorem length_check (dst src : Slice U64) :
    Slice.len dst = Slice.len src ↔ dst.length = src.length := by
  constructor
  · intro same
    simpa using congrArg UScalar.val same
  · intro same
    exact UScalar.eq_of_val_eq (by simpa using same)

private theorem run_map (dst src : Slice U64) (transform : U64 → U64 → U64)
    (body : State U64 U64 × (State U64 U64 → State U64 U64) →
      Result (ControlFlow (State U64 U64 × (State U64 U64 → State U64 U64)) (State U64 U64)))
    (step : ∀ i, i < dst.length → ∀ back,
      body (stateAt dst src i, back) =
        Result.ok (ControlFlow.cont (stateAt dst src (i + 1),
          fun final => back (replaceLeft final i (transform dst[i]! src[i]!)))))
    (done : ∀ back, body (stateAt dst src dst.length, back) =
      Result.ok (ControlFlow.done (back (stateAt dst src dst.length)))) :
    (do
      let (left, restoreSlice) ← core.slice.Slice.iter_mut dst
      let (iter, restoreIter) ← bulksketch.core.iter.traits.iterator.Iterator.zip.trait_default
        (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT U64)
        (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U64) left src
      let final ← loop body (iter, fun state => state)
      Result.ok (restoreSlice (restoreIter final))) =
      Result.ok (mapFrom dst src transform 0) := by
  simp only [core.slice.Slice.iter_mut, bind_ok]
  dsimp! only
  rw [construct]
  simp only [bind_ok]
  dsimp! only
  rw [map_loop dst src transform body step done 0 (Nat.zero_le _) (fun state => state)]
  simp only [bind_ok, stateAt]

theorem square_slice_refines : PortableSliceChallenges.squareRefines := by
  intro dst src
  unfold square_slice
  simp only [length_check]
  split
  · rename_i same
    apply run_map
    · intro index bound back
      have rightBound : index < src.length := by omega
      change square_slice_loop.body dictionary (stateAt dst src index) back = _
      simp only [square_slice_loop.body, next_some_at dst src index bound rightBound, bind_ok]
      dsimp! only
      rw [Slice.Inhabited_getElem_eq_getElem! src index rightBound]
      change (do
        let squared ← bulksketch.field.gf64.square dictionary src[index]!
        Result.ok (ControlFlow.cont (stateAt dst src (index + 1),
          fun final => back (replaceLeft final index squared)))) = _
      rw [Square.square_refines]
      simp only [Bind.bind, bind_ok]
    · intro back
      change square_slice_loop.body dictionary (stateAt dst src dst.length) back = _
      simp only [square_slice_loop.body, next_done_at dst src dst.length (Or.inl (Nat.le_refl _)), bind_ok]
      dsimp! only
  · simp only [core.fmt.Arguments.from_str]
    exact bind_ok (() : core.fmt.Arguments) (fun _ => Result.fail Error.panic)

private theorem scaled_zero (left right : U64) :
    PortableSliceChallenges.scaleValue 0#u64 left right = left := by
  apply U64.bv_eq_imp_eq
  change left.bv ^^^ multiplyWord right.bv 0 = left.bv
  rw [multiplyWord_zero]
  simp

private theorem scaled_one (left right : U64) :
    PortableSliceChallenges.scaleValue 1#u64 left right = left ^^^ right := by
  apply U64.bv_eq_imp_eq
  change left.bv ^^^ multiplyWord right.bv 1 = left.bv ^^^ right.bv
  rw [multiplyWord_one]

theorem scale_xor_refines : PortableSliceChallenges.scaleRefines := by
  intro dst src scale
  unfold scale_xor
  simp only [length_check]
  split
  · rename_i same
    split
    · rename_i isZero
      subst scale
      congr 1
      apply Slice.ext_getElem (by simp)
      intro index bound mappedBound
      rw [Slice.Inhabited_getElem_eq_getElem! dst index bound,
        Slice.Inhabited_getElem_eq_getElem! _ index mappedBound,
        mapFrom_word dst src _ 0 index bound]
      simp [scaled_zero]
    · split
      · rename_i isOne
        subst scale
        -- The scale-one path reuses the original XOR call.
        rw [PortableXor.xor_assign_map dictionary dst src same]
        have sameTransform : PortableSliceChallenges.scaleValue 1#u64 =
            (fun left right : U64 => left ^^^ right) := by
          funext left right
          exact scaled_one left right
        rw [sameTransform]
      · apply run_map
        · intro index bound back
          have rightBound : index < src.length := by omega
          change scale_xor_loop.body dictionary scale (stateAt dst src index) back = _
          simp only [scale_xor_loop.body, next_some_at dst src index bound rightBound, bind_ok]
          dsimp! only
          rw [Slice.Inhabited_getElem_eq_getElem! src index rightBound,
            Slice.Inhabited_getElem_eq_getElem! dst index bound]
          change (do
            let product ← bulksketch.field.gf64.mul dictionary src[index]! scale
            let result ← lift (dst[index]! ^^^ product)
            Result.ok (ControlFlow.cont (stateAt dst src (index + 1),
              fun final => back (replaceLeft final index result)))) = _
          rw [native_mul_word]
          simp only [Bind.bind, bind_ok, lift]
          rfl
        · intro back
          change scale_xor_loop.body dictionary scale (stateAt dst src dst.length) back = _
          simp only [scale_xor_loop.body, next_done_at dst src dst.length (Or.inl (Nat.le_refl _)), bind_ok]
          dsimp! only
  · simp only [core.fmt.Arguments.from_str]
    exact bind_ok (() : core.fmt.Arguments) (fun _ => Result.fail Error.panic)

end BulksketchBridge.PortableSlice
