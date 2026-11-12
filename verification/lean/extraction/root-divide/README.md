# Original factor division

The stock checked capture retains the original `Roots::divide` body and
its typed exact-division application slot. All three generated artifacts
match the independent checked replay. The projector verifies the original
source, stock tools, command scope and exact raw generated body, as well as
the linked shared types and stage body. The read-only `Option::as_ref` view
has an explicit scoped binding.

`RootDivide.divide_refines` proves the complete original wrapper frame.
It accounts for both checked prices and charges, the nonexact division
return, both checked offset overflows, and both successful commits.
The success proof discharges the source casts, increments, affine
subtraction, and slice and stack writes from the stated caller bounds.
The returned work and raw scratch include the original callee effects
even when a subsequent charge or offset fails.

`RootDivide.native_divide_refines` binds the exact-division slot to
the proved original Dense wrapper and the descending division model.
The original div/rem source correspondence and caller-wide admission
remain explicit separate obligations.

```sh
python3 extraction/root-divide/project.py
python3 -O extraction/root-divide/project.py
cd bridge
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake build BulksketchBridge.RootDivideNative
```
