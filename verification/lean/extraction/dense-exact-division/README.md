# Original exact-division wrapper

The pinned stock capture keeps the original wrapper and scopes the
original div/rem method as an explicit typed application slot. All
three original generated files reproduce byte for byte under checked
Aeneas replay. The projector checks the source bytes, exact wrapper
and callee spans, the typed callee signature, checked command paths
and the verbatim compiled wrapper.

`DenseExactDivide.exact_divide_refines` proves both original return
paths under the exact div/rem result. It proves the quotient prefix
clear on nonzero remainder with the returned remainder and raw
scratch untouched. The div/rem body itself has a separate obligation.

```sh
python3 extraction/dense-exact-division/project.py
python3 -O extraction/dense-exact-division/project.py
```
