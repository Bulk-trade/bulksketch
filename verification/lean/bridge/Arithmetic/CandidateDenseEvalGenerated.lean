-- Exact stock checked Dense Horner dispatch declaration.
import Arithmetic.SliceKernelTypes

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false

namespace bulksketch

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::eval_many_into]:
    Source: 'src/poly/dense.rs', lines 155:4-157:5 -/
def poly.Dense.Insts.BulksketchPolyPolynomial.eval_many_into
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (coefficients : Slice Std.U64) (points : Slice Std.U64) (out : Slice Std.U64)
  :
  Result (Slice Std.U64)
  := do
  backendcontractBulkKernelsInst.horner_many coefficients points out

end bulksketch
