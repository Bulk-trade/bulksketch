# Native degree-three and degree-four product certificate

The frozen Charon LLBC contains the original `deg34::certificate` body and
its captured duplicate-check closure. The checked ended-projector leaf
extractor produces the two nested loops, validation closure, and wrapper.
The projector retains those declarations and the reverse inclusive-range
dictionary verbatim. It checks the shared type definitions and the reused
slice equality field. Scoped bindings model the standard iterator `any`
and the equality call through a mutable and a shared reference.

`Certificate.certificate_refines` proves the exact returned bit and
scratch slice. Wrong-length and invalid-root paths return false with the
original scratch. Otherwise the original descending loop computes the
monic product in the prefix and leaves the remaining scratch intact. The
proof covers representable root-length addition and requires scratch room
only on the path that reaches the prefix operation.

`Certificate.certificate_accepts_root_polynomial` characterizes acceptance
by the exact factor length, nonzero distinct roots, and the equality of
the ascending factor polynomial to the monic product of those roots in
GF64. Both theorems use the native multiplication callback contract. The
extraction and standard-library bindings are part of the source
correspondence boundary.

Run the projector from the repository root.

```sh
python3 verification/lean/extraction/degree-certificate/project.py
```
