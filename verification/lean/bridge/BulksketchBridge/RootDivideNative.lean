import BulksketchBridge.RootDivideNativeSpec
import BulksketchBridge.RootDivide

namespace BulksketchBridge.RootDivide

open Aeneas.Std Aeneas.Std.RootDivideRuntime
open DenseCoefficient RebuiltLfsr BmEntry
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.types
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial (exact_divide_into)

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem native_call_refines (division : DenseDivisionRuntime.DivRem) {K : Type}
    (kernels : BulkKernels K bulksketch.field.Gf64) (roots : Roots) (buffers : FactorWork)
    (law : DenseDivision.RefinesModel division kernels) (ready : NativeDivideReady roots buffers) :
    exact_divide_into division DenseGcd.dictionary kernels buffers.modulus
      (prefixSlice buffers.gcd roots.gcd_len.val)
      (prefixSlice buffers.work (roots.degree.val + 2))
      (tail buffers.work (roots.degree.val + 2)) buffers.raw =
      .ok (nativeCall roots buffers) := by
  let divisor := prefixSlice buffers.gcd roots.gcd_len.val
  let quotient := prefixSlice buffers.work (roots.degree.val + 2)
  let remainder := tail buffers.work (roots.degree.val + 2)
  have divisorLength : divisor.length = roots.gcd_len.val := by
    exact (prefix_length _ _).trans (Nat.min_eq_left ready.gcdRoom)
  have quotientLength : quotient.length = roots.degree.val + 2 := by
    exact (prefix_length _ _).trans (Nat.min_eq_left ready.workRoom)
  have remainderLength : remainder.length = buffers.work.length - (roots.degree.val + 2) :=
    tail_length _ _
  have positive : 0 < divisor.length := by rw [divisorLength]; exact ready.divisorPositive
  have nonzero : divisor[divisor.length - 1]! ≠ 0#u64 := by
    rw [divisorLength]
    exact ready.divisorNonzero
  have qRoom : buffers.modulus.length + 1 ≤ quotient.length := by
    rw [quotientLength]
    exact ready.quotientRoom
  have remRoom : buffers.modulus.length + 1 ≤ remainder.length := by
    rw [remainderLength]
    exact ready.remainderRoom
  have frame := DenseDivision.modeled_exact_divide division kernels law buffers.modulus divisor
    quotient remainder buffers.raw positive nonzero qRoom remRoom ready.rawRoom
  let result := DenseDivision.expectedDivRem buffers.modulus divisor quotient remainder buffers.raw
    (DenseDivision.divisorInverse divisor[divisor.length - 1]!)
  change exact_divide_into division DenseGcd.dictionary kernels buffers.modulus divisor quotient remainder buffers.raw =
    if result.1.2 = 0#usize then .ok (some result.1.1, result.2.1, result.2.2.1, result.2.2.2)
    else .ok (none, DenseDivision.cleared result.2.1 (buffers.modulus.length + 1), result.2.2.1, result.2.2.2) at frame
  change _ = Result.ok (exactDivisionResult buffers.modulus divisor quotient remainder buffers.raw)
  rw [frame]
  unfold exactDivisionResult
  change _ = Result.ok (if result.1.2 = 0#usize then _ else _)
  by_cases zero : result.1.2 = 0#usize <;> simp only [zero, ite_true, ite_false] <;> rfl

theorem native_divide_refines : ActualNativeRootDivide := by
  intro division K kernels roots buffers factors stack meter law ready admitted
  let call := nativeCall roots buffers
  have callNormal := native_call_refines division kernels roots buffers law ready
  have concrete : reached (exact_divide_into division) DenseGcd.dictionary kernels roots buffers
      call.1 call.2.1 call.2.2.1 call.2.2.2 := by
    unfold reached
    simpa only [call, Prod.eta] using callNormal
  have refined := divide_refines (exact_divide_into division) DenseGcd.dictionary kernels roots
    buffers factors stack meter ready.toDivideReady
    ⟨call.1, call.2.1, call.2.2.1, call.2.2.2, concrete⟩
    (by
      intro length quotient remainder raw start stop called startOk endOk
      have same := Result.ok_injective (callNormal.symm.trans called)
      have candidate : call.1 = some length := congrArg Prod.fst same
      have exactQuotient : call.2.1 = quotient := congrArg (fun output => output.2.1) same
      rw [← exactQuotient]
      exact admitted length start stop candidate startOk endOk)
  rw [refined]
  unfold expected
  split
  · rfl
  · dsimp! only
    rw [callNormal]
    rfl

end BulksketchBridge.RootDivide
