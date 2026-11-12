# Field-algebra source accounting

This analysis records the field-algebra proof state on 2026-11-04: 29 core statements and 36 bridge statements, totaling 65; 14 distinct source-generated native-body refinements; all 532 source-inventory records and all 344 executable obligations retained. The number of complete Rust refinements is zero, and `full_implementation_coverage_achieved` is false. The component record is `audit/field-algebra-checkpoint.json`; source associations are recorded in `bridge/obligations.json`. Aggregate verification is required in addition to these source associations.

The 14 source IDs consist of WorkMeter new/charge/used; portable spread/reduce/square/raw_mul/mul/frobenius; and maps trace/canonical_trace/quadratic_rows/quadratic_value/solve_quadratic. Frobenius is upgraded to the unmodded iteration theorem in the same existing source row, not counted twice. Every registry native item matches the source inventory span hash, fixed source-linkage mapping, exact generated function declaration/file and a registered frozen challenge/theorem pair. The generated declaration selectors were independently checked as exact anchored names, avoiding prefix matches with loop helpers.

No native function credit is assigned to period, modulus irreducibility, table literal certificates or helper proof functions. Those are recorded as separate mathematical evidence. At this revision, all 10 inverse-related inventory records are unproved, with no generated-body proof evidence; successful standalone extraction and the failed captured-closure pilot carry no proof credit.

The registry associates `actualValueMatchesAllChunkContributions` with the existing `MapsQuadratic.quadratic_value_refines` theorem. An earlier association named the nonexistent `MapsQuadraticValue.quadratic_value_refines`; correcting that association changed no proof or fixed proposition.

At this revision, the contracts specialize to the actual Gf64 dictionary and the word-model sum of 64 trace conjugates. They do not yet identify that trace with Mathlib `Algebra.trace` or establish the quotient representation. Compiler, runtime, ownership and ISA correspondence remain separate assumptions. Exact polynomial irreducibility is proved separately; the source mul theorem itself still does not use that result or close the field-representation bridge.

Source accounting does not replace elaboration, exact-statement and transitive-axiom auditing, or exported-term replay through the Lean kernel and Nanoda.
