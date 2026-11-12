# Original candidate scan and Dense Horner dispatch

`checked-candidates-nested-return-v1` consumes the original checked Charon
capture of `Execution::candidates` at `src/decode/stages.rs:266–303`. Stock
Aeneas rejects original LLBC return 500 inside the nested Zip. The pass
uses one fresh flag, ends the original Zip and Chunks storage at the
respective loop exits, and dispatches the same original result after both
loops. Only ordered `StorageDead` operations move across a loop join.
The original error enum constructors move to the error-only dispatcher.
The flag is false at every continuing state. A true flag exits both loops
and skips the original `Roots.count` assignment. Root and BM scratch
writes from earlier scan iterations are retained.

The source-scoped pass checks the function name, exact source span, original
edge identities, both storage epilogues, and the three enum constructors.
The scoped pass changes only `PrePasses.ml` and requires checked mode.
Stock, unchecked, and seven altered-scope fixtures reject at the original
nested-return guard. The unrelated checked affine splitter outputs match
byte-for-byte. The original Rust and captured LLBC are unchanged.

The candidate projection uses the already checked shared Zip and Chunks
bindings. The source calls the separately stock-captured original
`Dense::eval_many_into` and existing original `Execution::charge`.
The Dense method delegates directly to the supplied Horner backend.
No projected declaration imports a generated external axiom.

`project.py --kind inner` checks the two original inner loop declarations.
The default outer mode checks the two outer loop declarations and entry.
The dense mode checks the separately captured stock Dense dispatch.
