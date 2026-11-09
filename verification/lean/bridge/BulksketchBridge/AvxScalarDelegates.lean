import Arithmetic.AvxScalarDelegatesGenerated
import BulksketchBridge.X86Pclmul
import BulksketchBridge.RebuiltLfsrSpec

namespace BulksketchBridge.AvxScalarDelegates

open Aeneas.Std

open bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractArithmetic

namespace Pclmul
open bulksketch.backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic
export bulksketch.backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic
  (mul square frobenius inverse trace solve_quadratic raw_mul reduce)
end Pclmul

/-- Exact original Vpclmul512 scalar delegation at every field width. -/
def ActualNativeAvxScalarDelegates : Prop :=
  ∀ {F : Type} (field : bulksketch.field.BinaryField F),
    mul field = Pclmul.mul field ∧ square field = Pclmul.square field ∧
    frobenius field = Pclmul.frobenius field ∧ inverse field = Pclmul.inverse field ∧
    trace field = Pclmul.trace field ∧ solve_quadratic field = Pclmul.solve_quadratic field ∧
    raw_mul field = Pclmul.raw_mul field ∧ reduce field = Pclmul.reduce field

theorem native_avx_scalar_delegates : ActualNativeAvxScalarDelegates := by
  intro F field
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def ActualPclmulTraceDelegate : Prop :=
  ∀ {F : Type} (field : bulksketch.field.BinaryField F),
    Pclmul.trace field = bulksketch.field.maps.trace field

theorem pclmul_trace_delegate : ActualPclmulTraceDelegate :=
  fun _ => rfl

def ActualPclmulReduceDelegate : Prop :=
  ∀ {F : Type} (field : bulksketch.field.BinaryField F),
    Pclmul.reduce field = bulksketch.field.gf64.reduce field

theorem pclmul_reduce_delegate : ActualPclmulReduceDelegate :=
  fun _ => rfl

/-- The checked AVX source scalar square is the checked original PCLMUL
square and agrees with the original scalar GF64 body for every word. -/
def ActualNativeAvxScalarSquare : Prop :=
  ∀ input : U64,
    square X86Pclmul.dictionary input =
      bulksketch.field.gf64.square X86Pclmul.dictionary input

theorem native_avx_scalar_square : ActualNativeAvxScalarSquare := by
  intro input
  change Pclmul.square X86Pclmul.dictionary input = _
  exact (X86Pclmul.square_refines input).trans (Square.square_refines input).symm

theorem rebuilt_square_law {K : Type}
    (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (selected : kernels.ArithmeticInst.square = square X86Pclmul.dictionary) :
    RebuiltLfsr.squaringLaw kernels := by
  intro word
  rw [selected]
  exact native_avx_scalar_square word

#print axioms native_avx_scalar_delegates
#print axioms native_avx_scalar_square

end BulksketchBridge.AvxScalarDelegates
