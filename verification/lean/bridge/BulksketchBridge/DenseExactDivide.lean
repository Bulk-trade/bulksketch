import BulksketchBridge.DenseExactDivideSpec
import BulksketchBridge.RebuiltLfsr

namespace BulksketchBridge.DenseExactDivide

open Aeneas.Std DenseCoefficient RebuiltLfsr

theorem exact_divide_refines : ActualExactDivide := by
  intro division F K field kernels a b q rem qOut remOut raw rawOut qLen remLen called room
  by_cases zero : remLen = 0#usize
  · simp only [bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.exact_divide_into, called, bind_ok,
      zero, ite_true]
    rfl
  · have test : (remLen != 0#usize) = true := by simp [zero]
    have bound : (Slice.len a).val < qOut.length := by rw [Slice.len_val]; exact room zero
    have cut := inclusive_prefix qOut (Slice.len a) bound
    simp only [bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.exact_divide_into, called, bind_ok,
      zero, ite_false]
    dsimp! only
    simp only [test, ite_true, core.slice.index.Slice.index_mut, cut, bind_ok, fill_zero, Slice.len_val]
    rfl

end BulksketchBridge.DenseExactDivide
