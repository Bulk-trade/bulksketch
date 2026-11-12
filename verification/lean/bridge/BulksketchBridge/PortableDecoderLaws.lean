import BulksketchBridge.NativeTraceRecoveredFinish
import BulksketchBridge.NativeHonestBmDriver
import BulksketchBridge.AffineEnumerationHorner
import BulksketchBridge.PortableSlice
import BulksketchBridge.Algebra.WordLaws

namespace BulksketchBridge.PortableDecoder

open Aeneas.Std Algebra.Gf64
open RebuiltLfsr (portableField portableKernels)
open bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractArithmetic

theorem bm_raw : BmDiscrepancy.RawArithmetic portableKernels := fun _ _ => rfl

theorem bm_reduce : BmDiscrepancy.ReduceArithmetic portableKernels := fun _ => rfl

theorem bm_mul : BmMutable.NativeMul portableKernels := fun _ _ => rfl

theorem inverse : BmTerminal.NativeInverse portableKernels := fun _ => rfl

theorem raw_mul : DenseMulConvolutionSpec.RawMulAgrees portableKernels := fun _ _ => rfl

theorem square : DenseReducerSquare.SquareAgrees portableKernels := fun _ => rfl

theorem reduce : DenseMul.reduceAgrees portableKernels := fun _ => rfl

theorem mul_word : DenseDivRem.MulWordLaw portableKernels :=
  fun left right => native_mul_word left right

theorem direct_two : DirectTwo.CorrectArithmetic portableKernels :=
  ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem horner : AffineEnumerate.HornerLaw portableKernels :=
  AffineEnumerate.horner_law_of_portable portableKernels rfl

theorem exact_scale_xor : TimesXMod.ExactScaleXor portableKernels := by
  intro dst src scale aligned
  let output := MutableZip.mapFrom dst src (PortableSliceChallenges.scaleValue scale) 0
  refine ⟨output, ?_, MutableZip.mapFrom_length .., ?_⟩
  · change scale_xor portableField dst src scale = .ok output
    rw [PortableSlice.scale_xor_refines, ite_eq_left aligned]
  · intro index inside
    rw [MutableZip.mapFrom_word _ _ _ _ _ inside, ite_eq_left (Nat.zero_le index)]
    unfold PortableSliceChallenges.scaleValue
    rw [multiplyWord_comm src[index]!.bv scale.bv]

/-- The original default callback declines acceleration. The native Dense
fallback consequently computes the remainder. Both buffers are unchanged
at the callback boundary. -/
theorem reducer_square (modulus table : Slice U64) (degree : Nat) :
    DenseReducerAlgebra.CorrectTable modulus table degree →
      DenseReducerSquare.BackendSquareLaw portableKernels modulus table degree := by
  intro _ input dst raw _ width _
  refine ⟨false, dst, raw, rfl, width, rfl, ?_⟩
  intro impossible
  cases impossible

theorem paid_verification : ExecutionDriver.ActualPaidVerificationAccepts portableKernels :=
  ExecutionDriver.native_portable_paid_verification

end BulksketchBridge.PortableDecoder
