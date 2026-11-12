import BulksketchBridge.RootSetup
import BulksketchBridge.RawMulTable
import Mathlib.Tactic.NormNum

namespace BulksketchBridge.RootDivideArithmetic

open Aeneas.Std BulksketchBridge

theorem multiply_fits (pending stride : Usize) (room : pending.val * stride.val ≤ Usize.max) :
    ∃ start : Usize, Usize.checked_mul pending stride = some start ∧
      start.val = pending.val * stride.val := by
  obtain ⟨value, normal, exactValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.mul_spec (x := pending) (y := stride) room)
  refine ⟨value, ?_, exactValue⟩
  change Option.ofResult (pending * stride : Result Usize) = some value
  rw [normal]
  rfl

theorem add_fits (start length : Usize) (room : start.val + length.val ≤ Usize.max) :
    ∃ stop : Usize, Usize.checked_add start length = some stop ∧
      stop.val = start.val + length.val := by
  obtain ⟨value, normal, exactValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := start) (y := length) room)
  refine ⟨value, ?_, exactValue⟩
  simp only [Usize.checked_add, core.num.checked_add_UScalar, normal, Option.ofResult]
  rfl

theorem offset_word (value : Usize) :
    U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from value =
      .ok (.Ok (UScalar.cast .U64 value)) := by
  have bound := value.hBounds
  change value.val < 2 ^ System.Platform.numBits at bound
  have room : value.val ≤ UScalar.max .U64 := by
    rw [UScalar.max_UScalarTy_U64_eq, U64.max_eq]
    rcases System.Platform.numBits_eq with width | width <;> rw [width] at bound <;> omega
  change core.num.tryFromUScalar .U64 value = _
  rw [core.num.tryFromUScalar, ite_eq_left room]


end BulksketchBridge.RootDivideArithmetic
