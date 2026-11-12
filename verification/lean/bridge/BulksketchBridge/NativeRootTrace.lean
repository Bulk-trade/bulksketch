import BulksketchBridge.RootTraceWrapper
import BulksketchBridge.DenseReducerSquareAlgebra

namespace BulksketchBridge.RootTrace

open Aeneas.Std DenseReducerAlgebra DenseReducerSquare
open DenseMulConvolutionSpec
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.types

abbrev nativeSquare : RootTraceRuntime.ModularSquare :=
  bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into

/-- Exact original trace stage with its original Dense modular square
callback. The table invariant and exact kernel contracts discharge the
modular-square premise in the scoped trace projection. -/
def ActualNativeTrace : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) (roots : Roots)
    (buffers : FactorWork) (meter : WorkMeter),
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    4 ≤ buffers.modulus.length → buffers.modulus.length = buffers.trace.length + 1 →
    buffers.modulus[buffers.trace.length]! = 1#u64 →
    buffers.table.length = buffers.trace.length * (buffers.trace.length / 2) →
    CorrectTable buffers.modulus buffers.table buffers.trace.length →
    BackendSquareLaw kernels buffers.modulus buffers.table buffers.trace.length →
    ∃ first paidMeter,
      bulksketch.decode.roots.charge meter (.Trace roots.degree) = .ok (first, paidMeter) ∧
      match first with
      | .Err failure =>
        Roots.trace nativeSquare gf64 kernels roots buffers meter =
          .ok (.Err failure, roots, buffers, id, paidMeter)
      | .Ok () =>
        TraceReady roots buffers →
        if roots.checked then
          ∃ writes : TraceWrites, writes.correct roots buffers ∧
            Roots.trace nativeSquare gf64 kernels roots buffers meter =
              .ok (writes.frame roots buffers true (.Ok (.Ok .Gcd)) paidMeter)
        else
          ∃ second splitMeter,
            bulksketch.decode.roots.charge paidMeter (.SplitCheck roots.degree) = .ok (second, splitMeter) ∧
            match second with
            | .Err failure =>
              ∃ writes : TraceWrites, writes.correct roots buffers ∧
                Roots.trace nativeSquare gf64 kernels roots buffers meter =
                  .ok (writes.frame roots buffers false (.Err failure) splitMeter)
            | .Ok () =>
              ∃ writes : TraceWrites, writes.correct roots buffers ∧
                let accepted := decide (DenseCoefficient.prefixSlice writes.gcd roots.degree.val = writes.trace)
                let reply : core.result.Result Stage DecodeFailure := if accepted then .Ok .Gcd else .Err .NotSplit
                Roots.trace nativeSquare gf64 kernels roots buffers meter =
                  .ok (writes.frame roots buffers accepted (.Ok reply) splitMeter)

theorem native_trace_refines : ActualNativeTrace := by
  intro K kernels roots buffers meter rawLaw squareLaw reduceLaw minimum shape monic tableLen tableCorrect backend
  obtain ⟨first, paidMeter, charged, result⟩ := trace_wrapper_refines nativeSquare kernels roots buffers meter
  refine ⟨first, paidMeter, charged, ?_⟩
  cases first with
  | Err error => exact result
  | Ok paid =>
    cases paid
    intro ready
    exact result ready (native_modular_square kernels rawLaw squareLaw reduceLaw
      buffers.modulus buffers.table buffers.trace.length minimum shape monic tableLen tableCorrect backend)

end BulksketchBridge.RootTrace
