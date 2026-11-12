# Original sum_costs and the shared slice try_fold

The pinned original Charon capture stops at the generic
`Iterator::try_fold` associated output equality in stock Aeneas.
The exact-hash transformation binds only that one concrete standard
call and retains the shared slice, mutable iterator reborrow, original
u64 accumulator and actual closure. The stock Aeneas run still checks
the transformed LLBC. The now unused generic Try dictionary groups
stay present for builtin resolution and are excluded from extraction.

The Lean std slot follows the pinned Rust default iterator loop using
the stock shared slice iterator model. The source closure and caller
remain generated. The proof preserves the first error and the cursor
after its failing item. Physical Rust pointer semantics and the
standard-library slice iterator correspondence use the existing
modeled boundary.

Run the projector from the verification directory.

```sh
python3 extraction/sum-costs/project.py
```
