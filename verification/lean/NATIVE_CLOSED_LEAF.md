# Native closed-leaf recovery and Newton normalization

The ledger retains 344 native executable obligations and records 95 original
Aeneas body refinements under their stated contracts. Five source-linked LLBC
contracts remain separately checked. Production Rust is unchanged.

## Closed-leaf phases

For degree three and four the exact original prices are 640 and 2048 work
units for the solve phase, and 31 and 49 for factor verification. The
`roots::charge` refinement preserves the original pricing outcome and
applies the exact finite-word meter transition. A charge error preserves
the input state and workspace.

On the solve path, the original selected solver receives the factor
prefix and the four-word window at offset 11. The original split and
slice backward functions restore precisely that window. A miss returns
`ReducerPreparation` and the unchanged solver output. A hit records
the returned count and enters `FactorVerification`.

On the verification path, the original product certificate receives the
factor, the candidate window at offset 11 and the five-word product
window at offset 15. The proof checks the exact product scratch writeback
even when the certificate rejects. The checked bit is true exactly when
the candidate count is the degree, the candidates are distinct and
nonzero, and their monic product is the current GF64 factor. On acceptance
the caller appends precisely those words in the admitted roots interval,
increments the count and invokes the actual stack advance.

The original stage selector and stack advance have separate source
refinements. An empty stack returns `Verification` with the accepted
workspace and root state. An admitted pending frame restores its
coefficient prefix, degree, split direction and affine metadata, and
selects the exact next stage. The accepted-advance theorem composes
these two cases through the actual closed-leaf wrapper. The exact phase
equation retains the original advance result and backward continuation.

## Newton normalization

The original degree-three/four normalize loop and wrapper divide each
active low coefficient by the nonzero Newton denominator in cleared
word 5. They write the supplied syndrome into the penultimate coefficient
and one into the monic leading coefficient, preserving the exact scratch
suffix. The field theorem transports each result to GF64 under the
verified multiplication and inverse callbacks.

## Checked extraction and remaining coverage

Pinned Aeneas with checks emits both projections. The closed-leaf
projection uses the previously checked original solve and certificate
bodies for its two opaque application calls. The normalize projection
retains the original loop and wrapper. The pinned replay receipts bind
exact LLBC, generated files, native source fingerprints and tool commands.

Run `python3 scripts/verify_all.py` from `verification/lean` under the pinned
toolchain. The aggregate checks the frozen statements, transitive axioms,
both proof replays and the provenance rejection controls.

A separate checked extraction experiment emits the original Newton guard
and complete degree probe with transparent application bodies. Their
body proofs remain open. The isolated Berlekamp–Massey extraction still
requires a typed lowering for a mutable loop continuation and its paired
mirror writeback. General root recovery, other stage callers and accelerated
kernels, physical memory and ISA correspondence, and end-to-end decoder
completeness remain open.
