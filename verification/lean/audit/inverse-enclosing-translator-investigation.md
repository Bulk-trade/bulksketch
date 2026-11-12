# Enclosing inverse translation investigation

Date: 2026-11-06. Outcome: the existing pinned extractor still cannot translate the enclosing borrowed-square closure. No application source, generated application body or pinned translator source was edited. Every experiment here earns zero source-function proof credit.

## Reproduction and exact cause

The original canonical inverse-pilot LLBC has `has_errors=false`. Running the pinned Aeneas binary on it, with `-sequential -abort-on-error -print-error-emitters -log-debug InterpReduceCollapse,InterpLoopsFixedPoint`, reproduces the failure at maps.rs43–45. It is emitted by `src/interp/InterpReduceCollapse.ml:1373`, before `collapse_ctx_aux`.

The sequential diagnostic isolates the relevant borrow graph (identifiers are diagnostic names):

```text
abs@0 frozen: SL@0(closure { _0 = SB@1(^1) }, _)
abs@1 frozen: ignored_shared_loan(closure { _0 = SL@1(s@4 : T2, _) })
abs@2 endable: SB@0(^0), SL@2(closure { _0 = SB@1(^3) }, _)
```

At loop-entry preparation, `InterpJoin.reborrow_ashared_loans` duplicates the immutable outer closure loan into fresh abstraction abs@2. The duplicate retains a concrete shared borrow of the captured square callback. `collapse_ctx` deliberately rejects any non-frozen shared loan whose shared value contains concrete borrows. Its own comment points at the limitation in `InterpMatchCtxs.compute_abs_borrows_loans_maps`: concrete nested borrow identifiers cannot yet be registered in the abstraction maps. Deleting the guard would expose an unsupported representation; it would not establish sound translation.

This is specifically the captured `&square` inside the shared closure reference. The standalone inverse_with_frobenius routine accepts abstract callbacks directly and does not introduce this same nested captured-borrow loop. Its successful extraction therefore does not clear the enclosing wrapper.

## Controlled compiler-pass experiments

All experiments read the exact original source. A separate target/output directory avoids changing the active proof artifacts.

| Experiment | Charon result | Aeneas result |
| --- | --- | --- |
| Pinned original LLBC, sequential diagnostics | Existing complete LLBC | Reproduced nested shared-loan guard |
| Original inverse root, optimized MIR, explicitly enable Inline and ForceInline | Success | Additional unsupported outer-loop continue and inlined raw-pointer metadata/ub_checks; no complete generated artifact |
| Original inverse_using root, same inline passes, release debug assertions and UB checks disabled | Success | Inlined ub_checks still appears, followed by opaque Rev ADT aggregate failure; no complete generated artifact |

Charon explicitly sets mir_opt_level=0 in its driver; merely passing a higher optimization level does not enable inlining. The experiments explicitly enabled the MIR inline passes. The resulting LLBC is materially different and is not substituted into the active frozen arithmetic package. Release/check options are recorded as exploratory compiler configurations, not evidence that compiler correctness has been formally proved.

## Upstream evidence

Official upstream commit [fc321a2 / PR1457](https://github.com/AeneasVerif/aeneas/commit/fc321a28317f458338ce01fe684927eae0fa8f9e) introduced this recoverable guard and its explanation. The pinned source already includes it. The official main head checked during this investigation was `4acbb6d73abe9082e45cf49ba6d6229a2c7d5836`; the latest history for InterpReduceCollapse still ends at that same guard addition. No available upstream fix for this exact case was found. This is a bounded checked-source observation, not a claim that all possible tool branches were searched.

Pinned primary sources: [InterpReduceCollapse](https://github.com/AeneasVerif/aeneas/blob/ab34bd28458a08c150b7cbf1873e59af74588138/src/interp/InterpReduceCollapse.ml#L1326), [InterpMatchCtxs](https://github.com/AeneasVerif/aeneas/blob/ab34bd28458a08c150b7cbf1873e59af74588138/src/interp/InterpMatchCtxs.ml#L22), [loop-entry preparation](https://github.com/AeneasVerif/aeneas/blob/ab34bd28458a08c150b7cbf1873e59af74588138/src/interp/InterpLoopsFixedPoint.ml#L43), and [shared-loan reborrowing](https://github.com/AeneasVerif/aeneas/blob/ab34bd28458a08c150b7cbf1873e59af74588138/src/interp/InterpJoin.ml#L18).

## Bounded candidate work, requiring separate soundness review

1. Build a minimal translator regression containing a borrowed callback captured by a shared closure and invoked inside a counted loop, together with aliasing/nested-reference negative cases. Keep it outside native BulkSketch source.
2. Prefer a narrowly justified change to loop-entry reborrowing for immutable shared-only capture graphs, or implement correct nested shared-borrow registration in abstraction matching. Such a change must preserve the identity of the underlying loan, assign fresh shared-instance IDs on copies, maintain parent-region relationships and respect ended-loan conditions. It must not simply freeze arbitrary abstractions or erase borrow structure.
3. Re-run Aeneas invariant checks, positive/negative translator fixtures, original enclosing wrapper extraction, deterministic declaration/body linkage and both proof checkers. A versioned translator change would expand the reviewed extraction TCB and must be recorded explicitly before any new native proof credit.

No frontend patch was attempted in this checkpoint. The failed enclosing source obligations remain in the full native denominator. An opaque replacement closure or a manually asserted callback-normality fact would conceal the gap and is not an acceptable substitute.

## Original-source monomorphization pilot

A subsequent bounded pilot tested Charon monomorphization without a fabricated
Rust adapter. The Aeneas preset rejects combination with monomorphization because
of tuple representation; removing that option exposes incompatible operation
and index call-lowering options. Plain monomorphization from original public
`decode_into`, generic `inverse`, and explicit `inverse<Gf64>` selectors returns
success and `has_errors=false`, but each output contains zero function
declarations. Empty extraction is not a successful inverse translation.

The native public decode paths remain generic over the field; no suitable
existing monomorphic native-source caller was found. A real consumer
instantiation could provide a concrete callgraph, but the representation
lowering still needs a supported route. The nine exact commands, statuses and
artifact fingerprints are preserved in
[monomorphization-pilot-receipt.json](../extraction/inverse-chain/monomorphization-pilot-receipt.json).
This pilot changes no source, stable proof or pinned tool and earns zero credit.

## Durable local experiment evidence

Full command receipts and diagnostics are saved at `/workspace/bulk/bulksketch-pr-20261104/word-quotient-research/`. This directory is research evidence, not an active proof input.

| Evidence | SHA-256 |
| --- | --- |
| `/workspace/bulk/bulksketch/verification/lean/extraction/canonical-arithmetic/inverse-pilot/arithmetic.llbc` | `cd5efbbf9c68a8283359a2d48ffded1d60560df82374e131201a248106ebac7e` |
| `/workspace/bulk/bulksketch-pr-20261104/word-quotient-research/baseline-diagnostics/log.txt` | `5ec93bec26e2a7d9bcf1c326a13890d3f8561a0c0c2aa3f07de0f398e98daebe` |
| `/workspace/bulk/bulksketch-pr-20261104/word-quotient-research/sequential-diagnostics/log.txt` | `37aea5df3e92d43283242ac40ba698d72e82337c7827b32a02dce7edb252ca50` |
| `/workspace/bulk/bulksketch-pr-20261104/word-quotient-research/inline-enabled/arithmetic.llbc` | `fd9fc5eeaa25e4fb08b86404005c122ba3bf0628db69f0de0f3acbd295bb04bc` |
| `/workspace/bulk/bulksketch-pr-20261104/word-quotient-research/inline-aeneas/log.txt` | `7062a1bc99cbd3dab2bc80df4fe1deb056305b70e9a0c52bc7ac62ca18bf6a64` |
| `/workspace/bulk/bulksketch-pr-20261104/word-quotient-research/inline-release-generic/arithmetic.llbc` | `aab7e6288ef7c850d3c8d4fd80b085dbcc3dfe6b64ac2412b0b4b4544e261e36` |
| `/workspace/bulk/bulksketch-pr-20261104/word-quotient-research/inline-release-generic/aeneas.log` | `b2cb28f256154dc3b63255b6146ba207b85608a8fb574cb594a66c2e1dc62b2a` |
