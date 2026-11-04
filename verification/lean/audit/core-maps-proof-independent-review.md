# Independent core Maps proof review

Approved2026-11-04; no blockers. Exact hashes are recorded in core-maps-proof-review.json. The frozen MapsSpec/MapsChallenges/FieldTables meanings are unchanged. The root owns scoped/aggregate dual replay; this review ran no competing builds/checkers.

MapsCertificates contains eight exhaustive finite propositions proved with decide+kernel: all4096source-row/column coefficients; all256chunk entries; complete64basis images for chunk/matrix, trace selector, bothinverse projections, traceQ and freebit0. No certificate is an assumed oracle or native-evaluation axiom. The separately extracted columns are therefore checked against every original row coefficient.

Maps proves zero/XOR preservation for all relevant word maps, including chunkPrefix at every count<=16 using the complete per-entry matrix theorem. The previously checked generic64basis extensionality then lifts finite basis equalities to universal word equalities. These are not sampled tests or an enumeration of2^64words.

The Horner trace recurrence is connected to the independently defined XOR sum of all64conjugates by a general all-natural-count induction. The bit selector then agrees universally by linearity and its complete basis certificate. Right/left quadratic inverse identities give exactly the frozen trace-bit63 and freebit0 projections, with the polynomial square map Q defined independently of the tables. TraceQ=0 and chosen solution bit0=0 are separately established universally.

Solvability iff tracezero is DERIVED: any solution has zero trace via traceQ; conversely the checked matrix value solves Qz=a when the trace projection correction vanishes. Normalized uniqueness follows from the proved left inverse and the solution equation/freebit condition, without assuming injectivity, rank or uniqueness. No irreducibility or successful native result appears as a premise.

These are mathematical bitword/table theorems. Native source refinements must separately connect actual generated endpoints and data to these models; the native polynomial quotient representation/whole-library verification scope is not enlarged merely by this review.
