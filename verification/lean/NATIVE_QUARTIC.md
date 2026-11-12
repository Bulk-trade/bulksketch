# Native affine quartic, reciprocal quartic and solve frames

The ledger retains 344 native executable obligations. This checkpoint records
90 original Aeneas body refinements under their stated contracts and five
separate source-linked LLBC contracts. The production Rust is unchanged.

## Affine quartic

The original affine helper returns normally under the checked GF64 callback
equations. It rejects a zero linear coefficient and requires its original
cubic kernel and product certificate. The exact slice iterator reads the
three kernel words and selects their unsigned minimum. The proof covers all
three normalized quadratic calls and retains the four returned words in
source order.

Write (q_u(z)=z^2+uz). If the chosen kernel root is (u), the source computes
(v=b+u^2) and verifies (uv=c). The quartic becomes (q_v(q_u(z))+d).
The certificate provides a second nonzero kernel root distinct from (u).
Its image under (q_u) is (v), so any root of the affine quartic supplies
preimages in both distinct fibers. The three exact normalized quadratic
solves find representatives of those fibers. Their two translates by (u)
give four distinct roots. Thus, after the original kernel gate, the helper
succeeds exactly when the affine quartic has a root.

## General quartic

The original wrapper returns the exact affine result when its cubic
coefficient is zero. Otherwise it computes a shift (s) from two
31-step Frobenius calls and a square. The field period proves
(as^2=c). Translation by (s) gives the polynomial
(z^4+az^3+(b+as)z^2+D), where (D=s^4+bs^2+d) is the original
polynomial evaluated at (s). The original guard rejects (D=0).
For $D \ne 0$, taking the reciprocal and dividing by (D) gives exactly
the affine coefficients passed to the original helper.

The forward loop computes the three prefix products. The reverse loop
reads each original root before replacing it and updates the running
inverse with that old value. The checked word and field proofs show that
each returned word denotes the corresponding inverse plus the shift.
The affine reciprocal roots are nonzero because its constant term is
(D^{-1}). The inverse-plus-shift map preserves distinctness. The original
wrapper succeeds exactly when its recovery gate accepts and the monic
quartic has a root, and returns four distinct roots on success.

The original solve wrapper reads the degree and selects the cubic or
quartic path. On admitted four- and five-coefficient slices and sufficient
output space, a miss leaves the output unchanged. A hit returns the exact
degree, copies the original candidate array into the output prefix and
preserves the suffix. The frame theorem proves normal return under the GF64 callbacks and
uses the actual selected native call. Cubic candidate certification remains the separate
original product certificate.

## Checked extraction

The original quartic and solve closure extracts with the isolated
checked scalar-array retry. The retry applies during continuation-free
loop fixed-point list joins. When a concrete shared scalar-array loan
meets a concrete mutable loan of the same type, the retry ends the shared
side through the existing loan-ending path. The shared payload must have
no nested loans or borrows. Context matching, collapse and synthesis
joins retain their original modes. Pinned and unchecked controls reject
the original quartic join. The checked replay and the separate cubic and
certificate controls reproduce their three output artifacts byte for byte.

## Verification and remaining coverage

Run `python3 scripts/verify_all.py` from `verification/lean` with the pinned
toolchain. The aggregate checks the exact body projections, frozen types,
transitive axioms, Lean and independent Nanoda replay, and rejection
controls.

The isolated native Berlekamp–Massey experiment now passes full symbolic
evaluation with stock loan endings and writeback. Pure lowering still
rejects a nonzero abstraction level at `SymbolicToPureExpressions.ml:1288`.
That experiment has no coverage credit. Native Berlekamp–Massey, recovery
above the specialized quartic path, the remaining accelerated kernels and
physical memory and ISA correspondence still require proofs. End-to-end
decoder completeness remains open.
