# Independent original native trace proof review

Approved2026-11-04; no blockers. Exact hashes are recorded in native-trace-proof-review.json. This was read-only source reasoning, with no builds or edits.

The final trace_refines type is exactly the independently frozen unconditional challenge: every source U64 input and the real Gf64 dictionary produce Result.ok of the complete expected U8 selector. It does not assume successful return or a bounded/canonical input subset.

The fullGf64MASK proves canonicality for every word. The actual BITS64 branch is selected from the real dictionary, while the generic fallback remains present in the unchanged generated function. Both actual shifts61 and63 are below64 and have exact normal runtime equations for every input.

selector_bounded proves the XOR/AND result is at most1 using Nat.and_le_right. selector_conversion_normal discharges the general checked u64→u8 conversion condition and proves inner Rust Ok with exactly the expected full byte. The source expect therefore follows its success branch; no supplied Debug formatter or diagnostic assumption is needed. The concrete runtime models use full range-checked conversion, with error/formatting correspondence explicitly retained in the runtime/compiler trusted boundary. This proof does not use a successful-conversion stub.

The expected selector retains every byte bit: low bit is input coefficient61 XOR63 and all remaining bits are zero. The final simplification unfolds the original generated endpoint and expect definition only after the conversion is proved innerOk. It does not delete any original source branch.

This theorem establishes native selector behavior. The mathematical identification with the absolute trace of all64conjugates is a separate new MapsTraceMathChallenge, independently reviewed before proof search. Owner-reported targeted elaboration/axiom checks and parent aggregate kernel/Nanoda replay remain separate evidence; this source review does not assert those runs were repeated here.
