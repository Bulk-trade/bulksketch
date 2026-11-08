# Masked AVX-512 memory extraction

The checked x86_64 Apple Darwin extraction contains the original `mask`, `load` and
`store` from `src/backend/x86_vpclmul512.rs`. The receipt records the source and
tool revisions, target, selectors, extraction flags and hashes. Run
`python3 extraction/masked-memory/project.py` from `verification/lean` to check
the seven raw artifacts and the compiled diagnostic projection. The projection
retains the original load and store bodies verbatim and reuses the existing exact
mask definition. Its six external functions and register type are parameters.

## Pure extraction limits

`PureExtraction.pure_store_cannot_writeback` proves that every successful pure
store returns the slice saved by `as_mut_ptr` before the vector-dependent
instruction. Two values with different first lanes already require different
writeback for a one-word slice.

`PureExtraction.pure_load_cannot_read_two_words` proves that exact successful
loads of all two-word slices would inject 2¹²⁸ payloads into the
2⁶⁴ possible post-cast `ConstRawPtr I64` values. The source mask is
fixed at three for this length. Both obstructions quantify over all bindings
of the extracted pure signatures.

## Stateful model

`X86MaskedMemorySpec.lean` represents bytes in an admitted, non-wrapping
address window with separate write permissions. Reads and writes check the
bytes of active lanes. Loads zero inactive lanes and preserve memory. Stores
write the active lanes in little-endian order and preserve every other byte.
[Rust masked load specification](https://doc.rust-lang.org/core/arch/x86_64/fn._mm512_maskz_loadu_epi64.html)
and [Rust masked store specification](https://doc.rust-lang.org/core/arch/x86_64/fn._mm512_mask_storeu_epi64.html).

`X86MaskedMemory.lean` proves the byte behavior, readback and frame. It composes
the stateful model with the proved source mask for slice lengths zero through
eight. `X86MaskedMemoryRegister.lean` proves the equivalence of the paired
and flat register layouts. Its `store_register_payload` theorem reads back
the requested prefix from the updated memory and frames every address
outside that prefix. The scoped Lean replay recorded in `axiom-audit.log`
reports only `propext`, `Classical.choice` and `Quot.sound`.

Native body proof credit is zero for both wrappers. A source refinement needs
a checked lowering that preserves the slice address and write permission
through pointer construction and casting, executes the masked memory effect,
and returns the destination payload from the updated state. The modeled
address and permission window also needs a link to the Rust allocation and
borrow provenance.
