# Independent read-only Frobenius proof review

Reviewed2026-11-04 by wrapper_performance. No builds or source edits performed. Result: APPROVED; no blocking finding in the reviewed snapshot.

`bridge/BulksketchBridge/Frobenius.lean` SHA256 `b2d847306dd9e92facba0e383682abd0c0c95ebe7e19e0414cfb2e048997f324`.

Both independently frozen spec/challenge hashes remain unchanged: Spec `c6d1bca0bdadd3fc24de2890e26c9caf174d13ac87e6f0bc05301c334defe62a`; Challenges `ba780186bdf358b60c7a1f7eba108a3451d64e0a648a9de0c029d2ea97867d4f`. The active canonical generated Arithmetic.Funs SHA `99216822e5bf477e2063b48a3f2b7058fcd6582e0014dc640138b83c559e654b` matches the fresh extraction. The original generated endpoint and both loop/body definitions are present and used unchanged.

## Endpoint and exact result

`frobenius_refines` (lines109–128) has exactly the independent challenge type. It introduces every U64 input and every U32 power without any canonicality, successful-return, bounded-power, field-period or fabricated-dictionary premise. It names the actual generated Gf64 dictionary. The canonical-mask proof(lines101–105) correctly uses the actual full-width MASK. The source modulus operation is discharged using U32.rem_spec with divisor64 proven nonzero; remainderEq connects the resulting machine scalar to power.val%64 and Nat.mod_lt proves remainder<=63(lines112–118).

The endpoint then calls the proved source loop from start0 to that remainder. Its output equality preserves every64-bit coefficient of the frozen repeatedSquare model, not merely a reduced digest or numeric projection. No source body is substituted or declared opaque without its existing proof.

## Source loop and termination

`loop_refines`(lines30–99) proves the exact suffix for every ordered U32 range with end<=63. Those are helper preconditions and are fully discharged by the public endpoint. Its induction measure is end.val-start.val, a natural number.

In the active branch, the standard actual U32 range-next theorem gives normal advance, start+1 and unchanged end. Lines50–58 prove the next range remains ordered/bounded and the measure strictly decreases. Range start<end ensures advancing cannot overflow the source U32 counter. The original body executes the actual generated square, connected by the already-proved unconditional Square.square_refines theorem. The recursive suffix is invoked at that exact advanced iterator and actual square result. The elementary repeatedSquare_after_square lemma(lines22–26) aligns the recurrence by induction alone; it assumes no finite-field algebra or period.

In the exhausted branch(lines84–99), actual range-next returns None and unchanged range. The body returns the current input without attempting square. The zero remaining count gives the identity recurrence. `normal_of_spec`(lines15–20) uses total-WP elimination: effect and divergence cases are contradictory, so it obtains an actual Result.ok witness rather than assuming success.

## Scope and evidence limits

This proves source behavior after power modulo64 squarings. It does not prove64 squarings equal identity, irreducibility of the modulus, or exponent-reduction algebra for an unmodded requested power. The proof imports only the already-checked square refinement plus the frozen word model; no such period theorem is used implicitly.

The extraction/runtime-standard-library/compiler/ownership/ISA trust boundary is unchanged. This review is source reasoning, separate from the owner-reported targeted build and axiom audit. Parent retains responsibility for frozen exact-type audit, independent kernel/Nanoda replay, source-item accounting and final PR integration. The generated loop helpers remain part of one native frobenius source item.
