import Arithmetic.DenseDivRemGenerated
import BulksketchBridge.RawMulTable

namespace BulksketchBridge.DenseDivRem

open Aeneas Aeneas.Std Result Error BulksketchBridge
open bulksketch.backend.contract
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial

set_option maxRecDepth 4096

private theorem last_positive (b : Slice U64) (positive : 0 < b.length) :
    bulksketch.DenseReducerTableRuntime.last b = .ok (some b[b.length - 1]!) := by
  unfold bulksketch.DenseReducerTableRuntime.last
  rw [List.getLast?_eq_getElem?]
  have bound : b.val.length - 1 < b.val.length := by change b.length - 1 < b.length; omega
  rw [List.getElem?_eq_getElem bound, List.Inhabited_getElem_eq_getElem! _ _ bound, ← Slice.getElem!_Nat_eq]

theorem empty_divisor {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (a b q rem : Slice U64) (raw : Slice bulksketch.types.RawProduct)
    (empty : b.length = 0) :
    div_rem_into field kernels a b q rem raw = .fail panic := by
  have emptyList : b.val = [] := List.length_eq_zero_iff.mp empty
  simp only [div_rem_into, bulksketch.DenseReducerTableRuntime.last, emptyList, List.getLast?_nil,
    bind_ok, core.option.Option.expect, Result.ofOption, bind_fail]

theorem inverse_rejected {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (a b q rem : Slice U64) (raw : Slice bulksketch.types.RawProduct)
    (positive : 0 < b.length) (notMonic : b[b.length - 1]! ≠ 1#u64)
    (rejected : kernels.ArithmeticInst.inverse b[b.length - 1]! = .ok none) :
    div_rem_into field kernels a b q rem raw = .fail panic := by
  simp only [div_rem_into, last_positive b positive, bind_ok, core.option.Option.expect,
    Result.ofOption, ite_eq_right notMonic, rejected, bind_fail]

theorem checked_size_overflow {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (a b q rem : Slice U64) (raw : Slice bulksketch.types.RawProduct)
    (positive : 0 < b.length) (inverse : U64)
    (inv : b[b.length - 1]! ≠ 1#u64 → kernels.ArithmeticInst.inverse b[b.length - 1]! = .ok (some inverse))
    (overflow : Usize.max < a.length + 1) :
    div_rem_into field kernels a b q rem raw = .fail integerOverflow := by
  have addition : (Slice.len a + 1#usize : Result Usize) = .fail integerOverflow := by
    change UScalar.tryMk UScalarTy.Usize ((Slice.len a).val + (1#usize).val) = _
    rw [Slice.len_val]
    have outside : ¬ UScalar.check_bounds UScalarTy.Usize (a.length + 1) := by
      rw [UScalar.check_bounds_eq_inBounds]
      rw [UScalar.inBounds]
      rw [Usize.max, Usize.numBits] at overflow
      omega
    change UScalar.tryMk UScalarTy.Usize (a.length + 1) = _
    simp only [UScalar.tryMk, UScalar.tryMkOpt, dite_eq_right outside, Result.ofOption]
  by_cases monic : b[b.length - 1]! = 1#u64
  · simp only [div_rem_into, last_positive b positive, bind_ok, core.option.Option.expect,
      Result.ofOption, ite_eq_left monic, addition, bind_fail]
  · simp only [div_rem_into, last_positive b positive, bind_ok, core.option.Option.expect,
      Result.ofOption, ite_eq_right monic, inv monic, addition, bind_fail]

theorem insufficient_buffers {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (a b q rem : Slice U64) (raw : Slice bulksketch.types.RawProduct)
    (positive : 0 < b.length) (inverse : U64)
    (inv : b[b.length - 1]! ≠ 1#u64 → kernels.ArithmeticInst.inverse b[b.length - 1]! = .ok (some inverse))
    (safeSize : a.length + 1 ≤ Usize.max)
    (short : q.length < a.length + 1 ∨ rem.length < a.length + 1 ∨ raw.length < a.length + 1) :
    div_rem_into field kernels a b q rem raw = .fail assertionFailure := by
  obtain ⟨size, added, value⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := Slice.len a) (y := 1#usize) (by rw [Slice.len_val]; exact safeSize))
  rw [Slice.len_val] at value
  change size.val = a.length + 1 at value
  have qCheck : size ≤ Slice.len q ↔ a.length + 1 ≤ q.length := by
    rw [UScalar.le_equiv, Slice.len_val, value]
  have remCheck : size ≤ Slice.len rem ↔ a.length + 1 ≤ rem.length := by
    rw [UScalar.le_equiv, Slice.len_val, value]
  have rawCheck : size ≤ Slice.len raw ↔ a.length + 1 ≤ raw.length := by
    rw [UScalar.le_equiv, Slice.len_val, value]
  by_cases monic : b[b.length - 1]! = 1#u64
  · simp only [div_rem_into, last_positive b positive, bind_ok, core.option.Option.expect,
      Result.ofOption, ite_eq_left monic, added, massert, ge_iff_le, qCheck, remCheck, rawCheck]
    split_ifs <;> first | omega | simp only [bind_ok, bind_fail]
  · simp only [div_rem_into, last_positive b positive, bind_ok, core.option.Option.expect,
      Result.ofOption, ite_eq_right monic, inv monic, added, massert, ge_iff_le, qCheck, remCheck, rawCheck]
    split_ifs <;> first | omega | simp only [bind_ok, bind_fail]

end BulksketchBridge.DenseDivRem
