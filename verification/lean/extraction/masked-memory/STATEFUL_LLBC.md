# Stateful interpretation of the frozen masked-memory LLBC

The scoped projector reads the original structured LLBC. It checks the
frozen Rust file and both source spans, the extraction and target pins, and
the declaration registry that defines the local types and exact callee IDs.
It decodes every normal-path statement into the corresponding Lean
interpreter instruction. Local slots, statement order, reborrow modes,
metadata projections and call operands come from the LLBC. The check
validates the original unwind cleanup lists and admits a terminal return.
The execution contracts cover normal paths under the stated preconditions.

The load reborrows the shared slice twice. The first reborrow supplies its
length to the verified mask. The second supplies the view to `as_ptr`.
The cast preserves the view's address when it changes the pointer's
element type. The masked intrinsic reads from that address and places the
register in the return local. The proof gives the exact loaded lanes,
zeroes in the remaining lanes and the original heap.

The store creates the original two-phase mutable reborrow and consumes it
with `as_mut_ptr`. It casts that pointer, then takes the original shared
reborrow to read the length and compute the mask. It copies the register
argument and consumes the three moved operands at the intrinsic. The
intrinsic updates the heap and writes Unit into the return local. The
proof reads the caller's payload at the original address in the updated
heap and establishes that every address outside the written prefix is
unchanged.

Run these checks from `verification/lean`.

```sh
python3 extraction/masked-memory/project_stateful.py
PYTHONDONTWRITEBYTECODE=1 python3 -O extraction/masked-memory/check_stateful_controls.py
cd bridge
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake build BulksketchBridge.X86MaskedMemoryLlbc
```

The negative controls bypass the frozen raw-file digest and exercise
projection of altered calls, borrow and pointer operands, omitted
instructions, return, target, cleanup and local types.

The interpreter is scoped to the accepted instructions and modeled
normal paths. The Python projection and the pinned LLBC extraction are
trusted source-link checks. The caller supplies the slice descriptor,
exclusive mutable access, valid active addresses and write permission.
The heap, fat pointer and intrinsic semantics model the required
correspondence. Physical pointer provenance, aliasing, unwinding,
compiler code generation and processor execution remain separate
obligations. These proofs count separately from original Aeneas body
refinements. The original pure extraction obstructions still apply.
