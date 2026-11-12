# Shape permission and bucket-count extraction

The stock checked capture retains the original `SketchShape::bucket_count` and
`SketchShape::permits_id` bodies. `project.py` checks the original Rust bytes,
LLBC, selectors, pinned tools, checked Aeneas command and byte-identical replay.
It compares the new permission declaration with
`bridge/Arithmetic/ShapePermissionGenerated.lean` and the exact bucket-count
declaration with the already compiled `bridge/Arithmetic/CandidateCompactGenerated.lean`.
Five shared types match their earlier compiled definitions.

The proof of the permission guard uses the existing original `bucket_for`
refinement. It covers out-of-range buckets, including zero-length shapes, before
any modulo. It then proves exact equality between the requested bucket and
the ID modulo the number of buckets. The shape leaf proof is independent of
the request-level dispatch that chooses a shape.
