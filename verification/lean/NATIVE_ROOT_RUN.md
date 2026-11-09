# Original root traversal stages and AVX square heap effects

All 344 native executable obligations remain in scope. This checkpoint
adds exact original Aeneas body refinements for `Roots::run`,
`Roots::divide`, the affine subspace offset, `affine::splitter`,
`affine::subspaces`, the preparation and enumeration wrappers, the
inner enumerator and selector, the affine multiple, the GF64 solve map and its table
construction, and the original AVX linear update, Horner paths and capacity-18 encoder.
Production Rust and Cargo inputs are unchanged.

The stock root-run projection retains the original dispatcher and
subspace offset helper. Its theorem checks the stage decisions, exact
workspace frames, and all admitted branches. The original leaf,
closed-leaf, trace, reducer table, GCD, factor division, splitter,
affine preparation and affine enumeration wrappers are bound in the
projection. The original selector, binary solve map, and candidate
enumerator are bound directly. The native dispatcher specialization
also instantiates the affine multiple and Dense div/rem with their
original bodies. The GCD stage uses the
admitted div/rem law and normalized remainder and retry conditions.
Table, GCD and affine split prices follow the original order of
checked operations, including intermediate overflow.

The splitter theorem checks the original setup, the complete coefficient
loop, prefix normalization and all slice writebacks. It binds the
original linear evaluation and Dense modular square bodies under the
field, reducer table and backend contracts. The field proof relates the
normalized output to both child cosets at every root of the factor in
the parent coset. It requires independence of the new basis direction.
The complete traversal still needs to establish and preserve those premises.

The affine subspace table proof checks the seed, both loops and exact
row writes. Over Mathlib's GF(2⁶⁴), each prefix row represents the
polynomial whose zero set is the binary span of those directions. The
proof starts with `A₀ = X` and establishes `Aᵣ₊₁ = Aᵣ² + Aᵣ(bᵣ)Aᵣ`.

Affine preparation checks the exact charge, the zero linear coefficient,
the solve-map rejection, both rank guards, and both successful stages.
The split path invokes the original subspace table implementation. Affine
enumeration checks the exact price, both candidate-result frames, the
bounded count increment and the original advance after success. The
inner enumerator proof checks the rank shift, scratch split, batch
boundaries, Gray points, Horner calls, exact candidate writes and final
count. The proved frame supplies the wrapper's candidate law under
admitted scratch and rank bounds. The original Portable, PCLMUL, and
AVX-512 Horner methods provide the field-evaluation law when installed
in the backend slot under their contracts. The completeness theorem
returns every factor root exactly once if the factor splits into
distinct nonzero roots in the affine coset and the directions are
independent. It verifies the count, the exact returned root set, and
both scratch widths.

The original GF64 solve-map proof checks native table construction,
the coefficient fold, pivot insertion and reduction, and exact kernel,
image and preimage writes. Its field interpretation proves the
returned base maps to the constant term. The complete image and kernel
span invariants prove that the original result is empty exactly when
the equation has no solution. A successful result gives independent
directions and represents the entire solution fiber. For a split
simple factor, divisibility by the returned affine multiple puts every
factor root in that fiber. The complete paid preparation theorem
excludes the zero linear coefficient guard, an empty solve, both rank
rejections, selector failure, and subspace table bounds failure.
It returns the original enumeration or splitting stage with
independent directions and a coset containing every factor root.
The split branch preserves the factor polynomial and writes back the
exact prefix annihilator rows. The paid split stage reads the original
rank row and returns the GCD-stage frame with both child root tests.

The original affine-multiple proof checks its buffer setup, pivot
search, both normalization loops, modular square, and returned
coefficient and scratch frames against a finite column trace. The
scoped checked translation closes only the matching row and witness
Zip lifetimes in the frozen capture. The occupied-diagonal invariant
rules out the original exhaustion panic and bounds the returned length
by the original polynomial width. A separate quotient-ring invariant
tracks the exact packed row witnesses through each native pivot and
store. It proves that the emitted polynomial is monic and divisible
by the input factor. The occupied quotient rows are independent
and span the earlier columns, so the first dependent column gives the
least-degree nonzero affine multiple. Over GF(2⁶⁴), a zero linear
coefficient would make that witness a square. For a squarefree input
its square root would be a smaller affine multiple, a contradiction.

The enumeration selector and its square-products helper check all
scalar inputs. Their proofs preserve the checked operation order,
including the rank cast, optional shift and multiplication, and
checked arithmetic overflow.

The original divide theorem checks both charge results, a nonexact
division, both checked offset overflows, and the affine and non-affine
commits. It returns the exact quotient and remainder scratch, pending
right-child coefficients, stack record, left modulus, meter, and stage.
The original Dense exact-division wrapper is bound to the proved div/rem
body in the specialization. The push proof preserves every earlier
pending coefficient word. The pop proof restores exactly the top
factor and preserves the remaining frames. The workspace budget
supplies the GCD scratch, affine matrices, and subspace table.
For a proper GCD, exact division returns a normalized positive-degree
quotient. The factor degrees sum to the parent degree and the live
degree budget bounds the next pending slot. At an admitted affine GCD
stage, the exact native coefficient count selects either proper
division or a retry in a smaller positive-rank coset. The successful
divide commit partitions the parent's root set by the split classifier
and preserves the recorded child bases and rank. The complete
depth-first traversal still needs to compose these steps. From the
admitted incoming count, degree and pending state, the original
Roots::start establishes the empty pending layout, root budget, basis
reset and exact locator copy. The native predictor proves both checked
Gaussian cost loops and computes the preferred degree mask as 0x7fff8.
Traversal start uses the original V3 preference for degrees 3 through 18. The native
reducer preparation returns the correct square table and reborrows
its exact source-written windows at the next stage.

The native paid proper-division dispatcher derives the exact quotient
from GCD divisibility. The live degree budget supplies both checked offsets,
the next pending slot and the affine base cell. Its returned state preserves
degree mass and strictly lowers the sum of squared live factor degrees.
For the non-affine trace branch, two distinct roots have different binary
trace bits in at least one of the 64 cached directions. On a nonproper GCD
the current trace bit agrees across the entire factor, extending the
earlier-direction invariant and excluding the terminal retry rejection.
For a split simple factor, the trace polynomial is idempotent modulo
the factor. The original paid split check compares two exact padded
slices representing that same polynomial. Both the already-checked
and first-check paths enter the native GCD stage with its classifier.
Both trace and affine split return a normalized prefix. The next GCD
reborrows the exact source-written slices. Its proper branch supplies
the normalized factor frame for divide, which preserves the product
of the active and pending factors. The degree-zero, -one and -two
leaf and the accepted small-degree certificate append exactly their
roots, then finish or restore the exact pending factor. These emissions
preserve the represented locator product, including affine enumeration.
The rank proof combines the live-degree potential with a bounded local
phase rank. Exact GCD retry consumes one affine or trace direction.

The original deflation stage performs the leading-coefficient seed,
reverse synthetic division, and exact remainder test for each candidate.
The charged entry checks the admitted scratch and restores both windows.
A failed root leaves its current locator in place and returns the source
rejection. Success uses the original traversal start and affine choice. Distinct
valid candidate roots exclude rejection and give an exact factorization
of the original locator into the removed linear factors and residual.
The checked translator variant ends the one shared roots iterator loan
at the exact source return join. Exact traversal entry derives the
admitted residual frame and degree budget, including the separate
zero-budget path with empty coefficient scratch.

The original candidate stage checks the native charge, bounded chunks,
the Dense delegate and zero-evaluation Zip scan. An excess hit returns
the original error with prior writes intact. A scoped checked translator
pass moves each iterator's exact cleanup before its join and carries the
early return through the two loops. Distinct supplied hints on a
fresh scan cannot overflow the locator degree. The exact candidate
and deflation calls use the original driver transitions and return the
admitted residual product. The checked stock driver also covers the
degree probe, original BM guard, state commit, progress and latched
error. The driver takes canonicalization as an explicit callable. The completed-result
wrapper preserves the unique frozen shared workspace loan through the
exact source switches and exposes only the admitted completed root prefix.
The checked canonicalization wrapper preserves the work charge, budget
rejection, exact two-word swap, mask and duplicate checks, and the
root prefix writeback. Longer slices use an explicit unsigned standard
library sort contract. The checked original finish loop follows a finite
native driver trace, keeps the exact return residual and composes
the mutable workspace callbacks in source order.

The original shared candidate normalizer performs a stable merge and
packs each modulo bucket as distinct nonzero hints. The row accessor
returns the exact corresponding payload slice. Native proper divide
and reducer preparation preserve a common locator-product invariant,
including the validity of every live factor and separation of the affine
table from the pending-factor slots. The completed-result theorem gives
exact locator root membership under the represented emitted product.
The original BM driver either latches its exact charge error or
accepts the exact support locator at the native constant-word guard.
The original candidate and deflate calls establish the full initial
traversal invariant. Given the terminal emitted product of a simple
nonzero locator, a paid canonicalization step and completed-result
borrow return its exact sorted roots.
The paid Trace stage also preserves the live traversal product and
table, extends the direction cache, and supplies the exact normalized
GCD trace prefix. Paid GCD preserves the same invariant on writeback
and decreases the continuation rank on every admitted successful
return, including the non-affine retry with the next trace direction.
The affine splitter supplies both child-coset tests in its exact GCD
window. Affine GCD supplies a proper division or a smaller positive-rank
coset preserving every active root. The ordinary leaf handles the zero,
linear, and quadratic cases, transferring the complete emitted product
to verification or restoring the exact pending factor at lower potential.
A ranked interface constructs the original finite drain trace, including
its error latch and ordered workspace callbacks. It bounds the root tail
by 208 times the square of the admitted degree budget plus 211 calls.
Paid affine enumeration has the same exact pop and terminal verification
outcomes. The original leaf and affine pops restore the saved direction,
affine base and rank, and keep the shared basis. The first charge of any
FactorWork stage exits with the original workspace and exact failed-charge
meter. Complete per-stage readiness and charge induction remain open.

The AVX square finite-heap theorem composes the zero fill, scalar
coefficient seeds, and the original masked LLBC load/store block
trace. Under the admitted allocation views, it preserves the input
and table and changes exactly the modeled words of the two mutable
slices. The captured x86 RawProduct layout uses stride 16, alignment
8 and word offsets 0 and 8. The verifier checks that specific layout
and rejects target and overlap mutations. The layout premise is
capture-specific. Actual Rust pointer provenance, compiled scalar
stores and full compiler-to-ISA correspondence remain open.

The original AVX linear update uses two overlapping masked loads before
each descending write. Its slice theorem gives the exact GF64 linear
coefficient update. The finite-heap theorem composes the checked
load and store contracts for every block, including the short block,
and preserves every byte outside the admitted slice.

The original AVX-512 Horner kernel and both wrappers check the complete
reverse coefficient fold in each lane, the empty-input zero fill, and
the final short masked chunk. Its allocated proof preserves every
byte outside the output and keeps the shared point view valid.
The existing scoped translator variant applies to the exact inner
kernel capture. The two wrapper captures use stock Aeneas.

The original AVX-512 capacity-18 encoder packs the 18 odd powers in
three registers and applies either one input or the XOR sum of two
inputs. Its proof checks all lane selectors, the 8/8/2 masked stores,
and preservation of every byte outside the written prefix. The
original single-base lookup reads eleven exact six- or five-bit
windows of the input word and XORs their rows. Its finite-heap proof
checks the captured contiguous insertion-table layout and every
masked read. The original static table generator now refines the exact
zero-initialized cell fold across its three nested loops, including the
original Frobenius square. The per-cell field proof and exact immutable
INSERT_BASES initializer supply the lookup and encoder's field values.
The allocated encoder proof composes the admitted table and output views,
keeps the table bytes unchanged and frames bytes outside the output prefix.
The original single-ID capacity-18 insertion and horizontal XOR now
have exact proofs. The public GF64 selector is checked through its
original free dispatcher. All empty, single-ID, sparse, and arbitrary
32-ID chunk branches are checked under explicit leaf contracts.
The degree-18 rebuilt verifier's multi-ID seed selects the tile path.
The modeled masked-load and register recurrence has an exact odd-power
sum over all tile IDs and zero padding lanes. The original AVX locator-update entry dispatches to the proved
vector update at the 64-bit field width. Other widths delegate to the
original scalar default under the supplied Portable dictionary.
The original AVX continuation consumes the exact inclusive lag loop
and eight-word blocks, masks inactive lanes, and stops at the first
mismatch. Each lag and current comparison window has an exact
finite-heap read contract. The AVX locator-update and continuation
proofs compose with the rebuilt verifier under its seed and square
contracts. The original tile now refines the executable initialization and row
folds, including both mutable iterator writebacks. The composition from
those folds to the odd-power sum now checks for every admitted tile.
For degree 18 the original dispatch selects the exact four-register
tile. Its seed, original locator update and original continuation
compose into the rebuilt verifier's acceptance theorem. The original
scalar AVX and PCLMUL delegate bodies now bind the scalar square
to that composition. An admitted original Verification entry
constructs the finite verification and canonicalization finish trace
using the exact native returned state, root slice and meter.
The same original tile dispatch covers every admitted rebuilt seed.
The seed width is at most the root count, so the original singleton and
sparse special cases are unreachable during rebuilding. Every admitted
GF64 degree has exact AVX, PCLMUL and Portable rebuilt-verifier acceptance under
the recorded backend and memory contracts. Original row configuration
and first affine preparation supply exact driver and traversal entry.
Proper affine division preserves both child cosets, saved metadata
and the earlier pending stack. The post-Dense assembly rejection and
post-trace split-check rejection preserve their exact original scratch
and failed-charge meter. The AVX update, square and scale proofs compose
the actual masked memory calls and frame bytes outside each admitted
destination window. The original trace and affine split each pass
their exact normalized window into GCD. The resulting state supplies
the proper-division frame or retains its reducer and direction
invariant for the next retry. Both consecutive root calls become
a successful segment of the original driver trace. The ranked drain
preserves their exact returned state, meter and callback composition.
The checked original root budget bounds every proper split tree under
the admitted u16 budget, using the six exact node prices.

The first non-affine reducer transition preserves the original empty
direction cache, prepares the exact table and establishes Trace agreement
at direction zero. Both original paid Verification branches transition
to Canonicalization exactly when every input odd word agrees with the
selected root support. The full encoder also checks the original
short-root guards before touching its scratch. The original Portable and
PCLMUL dictionaries supply the complete verification laws. The AVX
version retains masked load and store premises and the full encoder law.

The exact paid Verification tail drains through the original source
finish. A mismatch returns VerificationFailed after one paid call. An
accepted row with a valid distinct root prefix pays canonicalization and
returns the original Equal or sorted Decoded view with exact scratch.
The degree-three and degree-four solver handoff preserves the live
factor, supplies the exact candidate count on success and lowers phase
rank on fallback. The paid certificate either retains the live factor
for the reducer or emits the factor and restores the exact pending
continuation. Canonicalized completion supplies the publication writer's
admitted root prefix. The original public report outcome and bucket
count, combined with the exact writer and finalizer, expose the
committed decoded row and its optional leading zero.

An emitted honest support locator determines the exact selected root
support and its distinct nonzero prefix. Native workspace admission
supplies both verifier scratch bounds. After the original two paid
stages, the sorted returned words represent precisely that support.
The original tiny probe and public completion dispatch have checked
source refinements. The original shape permission guard returns the
precise bucket membership rule before publication. The original
ordered sum-cost caller binds the V1 and V2 work wrappers through the
scoped checked standard-library slice fold. V2 preserves both separately
checked probe reserves.

The non-affine splitter search follows the exact original Trace and
GCD calls until the first proper divisor. Every failed split advances
one direction. The source meter charges one pair per attempt and one
initial split check when required. The reservation proof accounts for
the exact remaining direction count, and the returned divisor frame
retains the trace classification and agreement needed by division.

The full original AVX encoder binds the width-18 fast path, width-32
singleton, and width-72 and width-89 const singleton kernels, plus
the proved sparse and tile paths. Paid full and rebuilt verification
now use these actual routes with explicit backend dictionary and
masked-memory contracts. The original frozen shape accessor and both
request permission methods supply the native publication predicate for
ordinary and independent borrowed rows.

The admitted original V3 row work wrapper now derives its verification
and affine prices, computes the original maximum preferred degree of
18, and checks every reserve guard and cumulative overflow in source
order. Its V2 call is bound to the original ordered sum. The non-affine
search and both paid division charges form one exact node trace,
preserve both child trace histories and fit the original node envelope
with the table allowance.

Run the complete gate from `verification/lean`.

```sh
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 python3 scripts/verify_all.py
```
