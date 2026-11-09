# Frozen sketch shape extraction

The original `FrozenSketch::shape` body was captured with stock pinned Charon
and Aeneas, including borrow checking and Aeneas sanity checks. The capture
keeps both original immutable `Arc::deref` calls. The projection checks the
source bytes, checked commands, original LLBC, byte-identical replay, compiled
function body, and seven reused record or field declarations.

The Lean theorem identifies the returned payload as the shape field of the
stored immutable state. It uses the existing `Arc := Id` value model from
`RowLocalGenerated` and models the two shared dereferences as successful
reads of that payload. Physical allocation, pointer provenance, reference
count updates and drop semantics are outside this value refinement.
