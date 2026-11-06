import BulksketchBridge.Algebra.TraceNativeChallenges
import BulksketchBridge.Algebra.Trace
import BulksketchBridge.MapsTraceMath
import BulksketchBridge.MapsCanonicalTrace

namespace BulksketchBridge.Algebra.Gf64

open Aeneas Aeneas.Std BulksketchProofs.Field

private theorem selector_byte_is_trace (input : U64) :
    Algebra.trace (ZMod 2) Field (toField input.bv) =
      ((MapsTrace.expectedWord input).val : ZMod 2) := by
  rw [native_selector_trace_transport, MapsTraceMath.trace_byte_case]
  cases Maps.traceBit input.bv <;> rfl

/-- The actual generated native trace returns normally with the entire byte
equal to the Mathlib scalar trace, and no upper output bit is set. -/
theorem native_trace_is_algebra_trace : TraceNativeChallenges.actualTraceIsAlgebraTrace := by
  intro input
  exact ⟨MapsTrace.expectedWord input, MapsTrace.trace_refines input,
    MapsTraceMath.selector_value_bounded input, selector_byte_is_trace input⟩

private theorem canonical_byte_eq_selector (input : U64) :
    MapsCanonicalTrace.expectedWord input = MapsTrace.expectedWord input := by
  rw [MapsTraceMath.trace_byte_case]
  apply U8.bv_eq_imp_eq
  change (Maps.absoluteTrace input.bv).setWidth 8 = _
  rw [Maps.absoluteTrace_eq_selector]
  cases bitCase : Maps.traceBit input.bv <;>
    simp [Maps.traceWord, bitCase]

/-- The original 63-step canonical-trace loop has the same exact algebra-trace
meaning, including all assertions, checked conversions and normal return. -/
theorem native_canonical_trace_is_algebra_trace :
    TraceNativeChallenges.actualCanonicalTraceIsAlgebraTrace := by
  intro input
  refine ⟨MapsTrace.expectedWord input, ?_,
    MapsTraceMath.selector_value_bounded input, selector_byte_is_trace input⟩
  rw [MapsCanonicalTrace.canonical_trace_refines, canonical_byte_eq_selector]

end BulksketchBridge.Algebra.Gf64
