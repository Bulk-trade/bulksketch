import BulksketchBridge.RootTraceLoop
import BulksketchBridge.Algebra.Trace
import Mathlib.Algebra.CharP.Algebra

namespace BulksketchBridge.RootTrace

open Aeneas.Std
open Algebra.Gf64 Polynomial
open scoped BigOperators

set_option maxRecDepth 4096

theorem trace_at_eq_sum (value : Field) (count : Nat) :
    traceAt value count = ∑ i ∈ Finset.range count, value ^ (2 ^ i) := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  induction count with
  | zero => simp [traceAt]
  | succ n ih =>
    rw [traceAt, ih, ← frobenius_def, map_sum]
    simp only [frobenius_def, ← pow_mul, ← pow_succ]
    rw [Finset.sum_range_succ']
    simp [add_comm]

/-- The pointwise result of the original source loop is Mathlib's finite
field trace in the exact GF64 quotient. -/
theorem trace_at_is_algebra_trace (value : Field) :
    traceAt value 64 = algebraMap (ZMod 2) Field (Algebra.trace (ZMod 2) Field value) := by
  rw [trace_at_eq_sum, algebra_trace_conjugate_sum]

end BulksketchBridge.RootTrace
