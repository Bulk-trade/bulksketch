# Original V1 row work budget

The checked source capture selects the original row-bound wrappers with
`sum_costs` as the only opaque function. The V1 projection retains the
original body and exposes that single callee as a typed parameter. The
projector verifies the argument and call adaptation and checks the
original work-price and root-bound declarations.

The V1 theorem binds the exact six-charge array to an explicit checked
fold contract, composes original BM and root prices, and retains the two
checked-addition error exits. The stock generic Iterator::try_fold
signature remains an extraction boundary for the source sum function.

```sh
python3 extraction/row-work-budget-v1/project.py
```
