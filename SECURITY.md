# Security

## Reporting a problem

Please report security problems privately through GitHub: open the repository's
**Security** tab and choose **Report a vulnerability**. Do not open a public
issue for a problem that could be exploited.

Include the input (or a way to generate it), the decode limits and plan you
used, and what you observed.

## What the library defends against

bulksketch is meant to decode sketches received from untrusted peers.

- **Parsing.** `SketchView::parse` takes explicit size limits and rejects
  malformed or non-canonical encodings before any allocation.
- **Work.** Every decode runs under a work budget (`DecodeLimits::max_work`)
  and a fixed scratch size. A request that would exceed the budget stops with
  the error `WorkLimitExceeded` and returns no rows. The budget counts
  operations, not time.
- **Output.** A decoded row is checked against every stored syndrome before it
  is returned. A row that cannot be decoded is reported as `Failed`; no partial
  result of that row is returned, and the other rows of the request are
  unaffected.

## What it does not defend against

- **A known splitter seed.** Root finding uses directions derived from the
  `Decoder` seed. An attacker who knows the seed can craft rows that cost many
  times an honest decode (the work budget still caps them). Use a secret seed.
  The seed is a mitigation, not a proven bound; see the README.
- **More differences than capacity.** Beyond capacity, another set can have
  exactly the same syndromes. No decoder can detect this, and the result can
  then leave out real differences. Size the capacity for the difference you
  expect. When the reconciled sets must be exactly equal, confirm it
  independently afterwards, for example by comparing a hash of each whole set;
  checking only the returned IDs cannot reveal IDs that were left out.
- **Timing.** The code is not constant-time. Do not sketch secret values.

The Lean proofs cover the portable decoder under the assumptions listed in
`verification/lean/README.md`. They do not cover wire parsing, the accelerated
backends end to end, or the candidate-hint and V3 routes.
