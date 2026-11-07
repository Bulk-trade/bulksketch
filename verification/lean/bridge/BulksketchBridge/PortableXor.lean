import BulksketchBridge.PortableXorChallenges
import BulksketchBridge.PortableZipMap

namespace BulksketchBridge.PortableXor

open Aeneas Aeneas.Std
open bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels
open BulksketchBridge.MutableZip

private theorem body_step (dst src : Slice U64) (sameLength : dst.length = src.length)
    (i : Nat) (bounded : i < dst.length) (back : State U64 U64 → State U64 U64) :
    xor_assign_loop.body (stateAt dst src i) back =
      Result.ok (ControlFlow.cont (stateAt dst src (i + 1),
        fun final => back (replaceLeft final i (dst[i]! ^^^ src[i]!)))) := by
  have sourceBound : i < src.length := by omega
  simp only [xor_assign_loop.body, next_some_at dst src i bounded sourceBound, bind_ok]
  dsimp! only
  simp only [lift, bind_ok, Slice.Inhabited_getElem_eq_getElem! dst i bounded,
    Slice.Inhabited_getElem_eq_getElem! src i sourceBound]

private theorem body_done (dst src : Slice U64) (back : State U64 U64 → State U64 U64) :
    xor_assign_loop.body (stateAt dst src dst.length) back =
      Result.ok (ControlFlow.done (back (stateAt dst src dst.length))) := by
  simp only [xor_assign_loop.body, next_done_at dst src dst.length (Or.inl (Nat.le_refl _)), bind_ok]
  dsimp! only

theorem xor_assign_map {F : Type} (field : bulksketch.field.BinaryField F)
    (dst src : Slice U64) (sameLength : dst.length = src.length) :
    xor_assign field dst src = Result.ok (mapFrom dst src (· ^^^ ·) 0) := by
  have lengths : dst.len = src.len := UScalar.eq_of_val_eq (by simpa using sameLength)
  have scanned : xor_assign_loop (stateAt dst src 0) (fun state => state) =
      Result.ok (stateAt (mapFrom dst src (· ^^^ ·) 0) src dst.length) := by
    unfold xor_assign_loop
    exact map_loop dst src (· ^^^ ·) (fun (iterator, back) => xor_assign_loop.body iterator back)
      (body_step dst src sameLength) (body_done dst src) 0 (Nat.zero_le _) (fun state => state)
  simp only [xor_assign, lengths, ite_true, core.slice.Slice.iter_mut, bind_ok]
  dsimp! only
  rw [BulksketchBridge.MutableZip.construct]
  simp only [bind_ok]
  dsimp! only
  rw [scanned]
  simp only [bind_ok, stateAt]

theorem xor_assign_refines : PortableXorChallenges.actualXorAssignReturnsFrame := by
  intro F field dst src
  constructor
  · intro sameLength
    refine ⟨mapFrom dst src (· ^^^ ·) 0, xor_assign_map field dst src sameLength,
      mapFrom_length _ _ _ _, ?_⟩
    intro i bounded
    rw [mapFrom_word dst src (· ^^^ ·) 0 i bounded, ite_eq_left (Nat.zero_le i)]
  · intro differentLength
    have lengths : dst.len ≠ src.len := by
      intro equal
      apply differentLength
      simpa using congrArg UScalar.val equal
    simp only [xor_assign, ite_eq_right lengths, core.fmt.Arguments.from_str]
    exact bind_ok (() : core.fmt.Arguments) (fun _ => Result.fail Error.panic)

end BulksketchBridge.PortableXor
