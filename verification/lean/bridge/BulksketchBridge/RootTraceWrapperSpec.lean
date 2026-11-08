import BulksketchBridge.RootTraceLoopSpec

namespace BulksketchBridge.RootTrace

open Aeneas.Std
open bulksketch.decode.roots bulksketch.backend.contract bulksketch.types

def cacheWellFormed (roots : Roots) (buffers : FactorWork) : Prop :=
  ∀ basis, buffers.basis.directions = some basis →
    1 ≤ buffers.basis.len.val ∧ buffers.basis.len.val ≤ 64 ∧
    cachePrefix roots.splitter_seed basis buffers.basis.len.val

def cacheInitialLength (buffers : FactorWork) : Nat :=
  if buffers.basis.directions.isSome then buffers.basis.len.val else 1

structure TraceReady (roots : Roots) (buffers : FactorWork) : Prop where
  counter : roots.attempts.val + 1 ≤ Usize.max
  direction : roots.direction.val < 64
  cache : cacheWellFormed roots buffers
  trace : 2 ≤ buffers.trace.length
  gcd : buffers.trace.length ≤ buffers.gcd.length
  raw : 2 * buffers.trace.length < buffers.raw.length
  compare : roots.degree.val ≤ buffers.gcd.length

abbrev TraceReply := core.result.Result (core.result.Result Stage DecodeFailure) DecodeError

structure TraceWrites where
  attempts : Usize
  basisLength : U32
  basis : Basis
  activeLength : Usize
  trace : Slice U64
  gcd : Slice U64
  raw : Slice RawProduct

def TraceWrites.correct (writes : TraceWrites) (roots : Roots) (buffers : FactorWork) : Prop :=
  writes.attempts.val = roots.attempts.val + 1 ∧
  roots.direction.val < writes.basisLength.val ∧
  writes.basisLength.val = max (cacheInitialLength buffers) (roots.direction.val + 1) ∧
  writes.basisLength.val ≤ 64 ∧
  cachePrefix roots.splitter_seed writes.basis writes.basisLength.val ∧
  writes.activeLength.val ≤ writes.trace.length ∧ writes.trace.length = buffers.trace.length ∧
  writes.gcd.length = buffers.gcd.length ∧ writes.raw.length = buffers.raw.length ∧
  traceInvariant buffers.modulus (basisWord roots.splitter_seed roots.direction.val) 64
    writes.activeLength writes.trace

def TraceWrites.frame (writes : TraceWrites) (roots : Roots) (buffers : FactorWork)
    (checked : Bool) (reply : TraceReply) (meter : WorkMeter) :
    TraceReply × Roots × FactorWork × (FactorWork → FactorWork) × WorkMeter :=
  (reply, { roots with attempts := writes.attempts, trace_len := writes.activeLength, checked },
    { buffers with trace := writes.trace, gcd := writes.gcd, raw := writes.raw, basis := ⟨some writes.basis, writes.basisLength⟩ }, id, meter)

/-- Total result of the original trace wrapper under admitted scratch and a
law for the explicitly scoped Dense modular-square slot. Source pricing
and metering determine both charge outcomes. Every paid trace has its
exact 64-conjugate evaluations and caller-visible scratch frame. -/
def ActualTraceWrapper : Prop :=
  ∀ (square : RootTraceRuntime.ModularSquare) {K : Type}
    (backend : BulkKernels K bulksketch.field.Gf64) (roots : Roots) (buffers : FactorWork)
    (meter : WorkMeter),
    ∃ first paidMeter,
      bulksketch.decode.roots.charge meter (.Trace roots.degree) = .ok (first, paidMeter) ∧
      match first with
      | .Err failure =>
        Roots.trace square gf64 backend roots buffers meter = .ok (.Err failure, roots, buffers, id, paidMeter)
      | .Ok () =>
        TraceReady roots buffers →
        ModularSquareLaw square backend buffers.modulus buffers.table buffers.trace.length →
        if roots.checked then
          ∃ writes : TraceWrites, writes.correct roots buffers ∧
            Roots.trace square gf64 backend roots buffers meter =
              .ok (writes.frame roots buffers true (.Ok (.Ok .Gcd)) paidMeter)
        else
          ∃ second splitMeter,
            bulksketch.decode.roots.charge paidMeter (.SplitCheck roots.degree) = .ok (second, splitMeter) ∧
            match second with
            | .Err failure =>
              ∃ writes : TraceWrites, writes.correct roots buffers ∧
                Roots.trace square gf64 backend roots buffers meter =
                  .ok (writes.frame roots buffers false (.Err failure) splitMeter)
            | .Ok () =>
              ∃ writes : TraceWrites, writes.correct roots buffers ∧
                let accepted := decide (DenseCoefficient.prefixSlice writes.gcd roots.degree.val = writes.trace)
                let reply : core.result.Result Stage DecodeFailure := if accepted then .Ok .Gcd else .Err .NotSplit
                Roots.trace square gf64 backend roots buffers meter =
                  .ok (writes.frame roots buffers accepted (.Ok reply) splitMeter)

end BulksketchBridge.RootTrace
