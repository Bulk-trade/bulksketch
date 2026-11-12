# Core field-map proof analysis

Analysis date: 2026-11-04. Current source fingerprints are recorded in `audit/frozen-inputs.json`.
The fixed MapsSpec, MapsChallenges and FieldTables propositions are unchanged.
This note describes the source argument; scoped and aggregate exported-term
replay are separate checks.

MapsCertificates contains eight exhaustive finite propositions checked by the
Lean kernel using `decide`: all 4,096 source row/column coefficients; all 256
chunk entries; and the complete 64 basis images for chunk/matrix equality, the
trace selector, both inverse projections, traceQ and freebit0. No certificate is
an assumed oracle or native-evaluation axiom. The separately extracted columns
are checked against every original row coefficient.

Maps proves zero and XOR preservation for the word maps, including chunkPrefix
at every count up to 16 using the complete per-entry matrix theorem. Generic
64-basis extensionality lifts finite basis equalities to universal word
equalities. This does not sample inputs or enumerate all `2^64` words.

The Horner trace recurrence is connected to an independently defined XOR sum of
all 64 conjugates by induction over every natural count. Linearity and the
complete basis certificate identify the bit selector with that sum. The right
and left quadratic inverse identities establish exactly the specified trace
projection on bit 63 and the free-bit projection on bit 0. The polynomial square
map Q is defined independently of the tables. The identities `traceQ = 0` and
chosen-solution bit 0 equal to zero are proved universally.

Solvability is derived in both directions. Every solution has zero trace by
traceQ. Conversely, the checked matrix value solves `Qz = a` when the trace
projection correction vanishes. The left-inverse identity, solution equation
and free-bit condition give normalized uniqueness without assuming injectivity,
rank or uniqueness. No irreducibility or successful native result is a premise.

These are mathematical bitword and table theorems. Native refinements must
connect the actual generated endpoints and data to the models. This analysis
alone does not establish a native polynomial quotient representation or
whole-library verification.
