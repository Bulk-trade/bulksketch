import Arithmetic.AvxSliceEntryGenerated

namespace BulksketchBridge.AvxSliceEntry

open Aeneas Aeneas.Std Result Error
open Aeneas.Std.AvxSquareRuntime
open bulksketch.backend.x86_vpclmul512
open bulksketch.field

def ActualAvxScaleXor : Prop :=
  ∀ (load : Load) (store : Store) (xor : AvxSliceKernelRuntime.Xor) (dst src : Slice U64) (factor : U64),
    scale_xor load store xor dst src factor = scale_kernel load store xor false dst src factor

theorem scale_xor_refines : ActualAvxScaleXor := fun _ _ _ _ _ _ => rfl

def ActualAvxSquareSlice : Prop :=
  ∀ (load : Load) (store : Store) (dst src : Slice U64),
    square_slice load store dst src = square_kernel load store false dst src

theorem square_slice_refines : ActualAvxSquareSlice := fun _ _ _ _ => rfl

private theorem length_guard (dst src : Slice U64) :
    dst.len = src.len ↔ dst.length = src.length := by
  constructor
  · intro h
    simpa only [Slice.len_val] using congrArg UScalar.val h
  · intro h
    apply UScalar.eq_of_val_eq
    simpa only [Slice.len_val] using h

/-- The original Arithmetic entry retains its length assertion and exact
field dispatch. Both fallback and native calls are bound to original bodies. -/
def ActualAvxScaleXorEntry : Prop :=
  ∀ (load : Load) (store : Store) (xor : AvxSliceKernelRuntime.Xor) {F : Type}
    (field : BinaryField F) (dst src : Slice U64) (factor : U64),
    Vpclmul512.Insts.BulksketchBackendContractArithmetic.scale_xor load store xor field dst src factor =
      if dst.length = src.length then do
        let bits ← field.BITS
        if bits != 64#u32 then
          bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.scale_xor
            field dst src factor
        else scale_kernel load store xor false dst src factor
      else .fail .panic

theorem scale_xor_entry_refines : ActualAvxScaleXorEntry := by
  intro load store xor F field dst src factor
  unfold Vpclmul512.Insts.BulksketchBackendContractArithmetic.scale_xor
  dsimp! only
  by_cases equal : dst.length = src.length
  · have same := (length_guard dst src).mpr equal
    simp only [ite_eq_left same, ite_eq_left equal, scale_xor_refines load store xor dst src factor]
  · have mismatch : dst.len ≠ src.len := fun h => equal ((length_guard dst src).mp h)
    simp only [ite_eq_right mismatch, ite_eq_right equal, core.fmt.Arguments.from_str]
    exact bind_ok (() : core.fmt.Arguments) (fun _ => Result.fail Error.panic)

def ActualAvxSquareSliceEntry : Prop :=
  ∀ (load : Load) (store : Store) {F : Type} (field : BinaryField F) (dst src : Slice U64),
    Vpclmul512.Insts.BulksketchBackendContractArithmetic.square_slice load store field dst src =
      if dst.length = src.length then do
        let bits ← field.BITS
        if bits != 64#u32 then
          bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.square_slice field dst src
        else square_kernel load store false dst src
      else .fail .panic

theorem square_slice_entry_refines : ActualAvxSquareSliceEntry := by
  intro load store F field dst src
  unfold Vpclmul512.Insts.BulksketchBackendContractArithmetic.square_slice
  dsimp! only
  by_cases equal : dst.length = src.length
  · have same := (length_guard dst src).mpr equal
    simp only [ite_eq_left same, ite_eq_left equal, square_slice_refines load store dst src]
  · have mismatch : dst.len ≠ src.len := fun h => equal ((length_guard dst src).mp h)
    simp only [ite_eq_right mismatch, ite_eq_right equal, core.fmt.Arguments.from_str]
    exact bind_ok (() : core.fmt.Arguments) (fun _ => Result.fail Error.panic)

#print axioms scale_xor_refines
#print axioms square_slice_refines
#print axioms scale_xor_entry_refines
#print axioms square_slice_entry_refines

end BulksketchBridge.AvxSliceEntry
