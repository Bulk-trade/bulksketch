import BulksketchBridge.RootTraceSpec
import BulksketchBridge.DenseCoefficientPolynomial
import BulksketchBridge.DenseGcdSpec
import Mathlib.Algebra.Polynomial.Div

namespace BulksketchBridge.RootTrace

open Aeneas Aeneas.Std
open bulksketch.decode.roots bulksketch.backend.contract bulksketch.types
open DenseCoefficient SliceKernels Algebra.Gf64 Polynomial

noncomputable def traceAt (value : Field) : Nat → Field
  | 0 => 0
  | k + 1 => traceAt value k ^ 2 + value

/-- The separately scoped modular-square application returns the original
output length and scratch shapes, with polynomial semantics modulo the
factor. The factor and table are fixed throughout the source trace loop. -/
def ModularSquareLaw (square : RootTraceRuntime.ModularSquare)
    {K : Type} (backend : BulkKernels K bulksketch.field.Gf64) (modulus table : Slice U64)
    (degree : Nat) : Prop :=
  ∀ input gcd raw, input.length ≤ degree → degree ≤ gcd.length → 2 * degree < raw.length →
    ∃ len squared scratch,
      square gf64 backend input modulus table gcd raw = .ok (len, squared, scratch) ∧
      len.val ≤ degree ∧ squared.length = gcd.length ∧ scratch.length = raw.length ∧
      slicePolynomial (prefixSlice squared len.val) =
        (slicePolynomial input ^ 2) %ₘ slicePolynomial modulus

def traceInvariant (modulus : Slice U64) (splitter : U64) (k : Nat)
    (len : Usize) (trace : Slice U64) : Prop :=
  ∀ x : Field, (slicePolynomial modulus).IsRoot x →
    (slicePolynomial (prefixSlice trace len.val)).eval x =
      traceAt (toField splitter.bv * x) k

/-- Every admitted suffix of the original Rust recurrence terminates,
preserves all scratch lengths, and gives the 64-term Frobenius trace at
every root of the original factor. Modular square is the explicit slot
that will be linked to the original Dense reducer. -/
def ActualTraceLoop : Prop :=
  ∀ (square : RootTraceRuntime.ModularSquare) {K : Type}
    (backend : BulkKernels K bulksketch.field.Gf64) (range : core.ops.range.Range U32)
    (len : Usize) (modulus trace gcd table : Slice U64) (raw : Slice RawProduct) (splitter : U64),
    1 ≤ range.start.val → range.start.val ≤ 64 → range.«end».val = 64 →
    2 ≤ trace.length → len.val ≤ trace.length → trace.length ≤ gcd.length →
    2 * trace.length < raw.length →
    ModularSquareLaw square backend modulus table trace.length →
    traceInvariant modulus splitter range.start.val len trace →
    ∃ output updated gcdOut rawOut,
      Roots.trace_loop1 square gf64 backend range len modulus trace gcd table raw splitter =
        .ok (output, updated, gcdOut, rawOut) ∧
      output.val ≤ updated.length ∧ updated.length = trace.length ∧
      gcdOut.length = gcd.length ∧ rawOut.length = raw.length ∧
      traceInvariant modulus splitter 64 output updated

/-- The exact update also certifies the normalized prefix passed to GCD. -/
def ActualTraceLoopWithNormal : Prop :=
  ∀ (square : RootTraceRuntime.ModularSquare) {K : Type}
    (backend : BulkKernels K bulksketch.field.Gf64) (range : core.ops.range.Range U32)
    (len : Usize) (modulus trace gcd table : Slice U64) (raw : Slice RawProduct) (splitter : U64),
    1 ≤ range.start.val → range.start.val ≤ 64 → range.«end».val = 64 →
    2 ≤ trace.length → len.val ≤ trace.length → trace.length ≤ gcd.length →
    2 * trace.length < raw.length →
    ModularSquareLaw square backend modulus table trace.length →
    traceInvariant modulus splitter range.start.val len trace →
    ∃ output updated gcdOut rawOut,
      Roots.trace_loop1 square gf64 backend range len modulus trace gcd table raw splitter =
        .ok (output, updated, gcdOut, rawOut) ∧
      output.val ≤ updated.length ∧ updated.length = trace.length ∧
      gcdOut.length = gcd.length ∧ rawOut.length = raw.length ∧
      traceInvariant modulus splitter 64 output updated ∧
      (range.start.val < 64 ∨ DenseGcd.Normal (prefixSlice trace len.val) →
        DenseGcd.Normal (prefixSlice updated output.val))

end BulksketchBridge.RootTrace
