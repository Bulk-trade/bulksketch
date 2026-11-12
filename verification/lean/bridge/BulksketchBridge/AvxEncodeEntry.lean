import Arithmetic.AvxEncodeEntryGenerated

namespace BulksketchBridge.AvxEncodeEntry

open Aeneas Aeneas.Std
open AvxInsertDispatchRuntime
open bulksketch.backend.contract
open bulksketch.backend.x86_vpclmul512
open bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

abbrev Insert := {F : Type} → bulksketch.field.BinaryField F → Batch

def expected {F K : Type} (fast : Batch) (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (odd ids : Slice U64) : Result (Slice U64) := do
  let bits ← field.BITS
  if bits = 64#u32 ∧ odd.length = 18 ∧ (ids.length = 1 ∨ ids.length = 2)
  then fast odd ids
  else BulkKernels.encode_nonzero.default kernels odd ids

/-- The original encoder calls the fast 18-word leaf only on the precise
width and count guard. Every other input uses the original default zero/fold
ordering, including both singleton calls when two IDs are supplied. -/
def ActualAvxEncodeEntry : Prop :=
  ∀ (fast : Batch) (insertModel : Insert) {F K : Type}
    (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F),
    insertModel field = kernels.insert_nonzero →
    ∀ odd ids, encode_nonzero fast insertModel field odd ids = expected fast field kernels odd ids

theorem avx_encode_entry : ActualAvxEncodeEntry := by
  intro fast insertModel F K field kernels insertEq odd ids
  have default0 (iter : core.slice.iter.Iter U64) (state : Slice U64) :
      encode_nonzero_loop0 insertModel field iter state =
        BulkKernels.encode_nonzero.default_loop kernels iter state := by
    simp only [encode_nonzero_loop0, encode_nonzero_loop0.body,
      BulkKernels.encode_nonzero.default_loop, BulkKernels.encode_nonzero.default_loop.body, insertEq]
    rfl
  have default1 (iter : core.slice.iter.Iter U64) (state : Slice U64) :
      encode_nonzero_loop1 insertModel field iter state =
        BulkKernels.encode_nonzero.default_loop kernels iter state := by
    simp only [encode_nonzero_loop1, encode_nonzero_loop1.body,
      BulkKernels.encode_nonzero.default_loop, BulkKernels.encode_nonzero.default_loop.body, insertEq]
    rfl
  have default2 (iter : core.slice.iter.Iter U64) (state : Slice U64) :
      encode_nonzero_loop2 insertModel field iter state =
        BulkKernels.encode_nonzero.default_loop kernels iter state := by
    simp only [encode_nonzero_loop2, encode_nonzero_loop2.body,
      BulkKernels.encode_nonzero.default_loop, BulkKernels.encode_nonzero.default_loop.body, insertEq]
    rfl
  have width : odd.len = 18#usize ↔ odd.length = 18 := by
    have literal : (18#usize).val = 18 := rfl
    constructor
    · intro h; simpa only [Slice.len_val, literal] using congrArg UScalar.val h
    · intro h; apply UScalar.eq_of_val_eq; simpa only [Slice.len_val, literal] using h
  unfold encode_nonzero expected
  refine congrArg (fun branch : U32 → Result (Slice U64) => Aeneas.Std.bind field.BITS branch) ?_
  funext bits
  by_cases bits64 : bits = 64#u32
  · by_cases size18 : odd.length = 18
    · simp only [bits64, width.mpr size18, size18, eq_self, true_and, ite_true, Slice.len_val]
      generalize ids.length = count
      cases count with
      | zero =>
        simp [bind_ok, default0, insertEq, BulkKernels.encode_nonzero.default]
      | succ count =>
        cases count with
        | zero => simp [bind_ok]
        | succ count =>
          cases count with
          | zero => simp [bind_ok]
          | succ count =>
            simp [bind_ok, default0, insertEq, BulkKernels.encode_nonzero.default]
    · have noWidth : odd.len ≠ 18#usize := fun h => size18 (width.mp h)
      simp only [bits64, noWidth, size18, eq_self, true_and, false_and, ite_false, ite_true,
        default1, insertEq, BulkKernels.encode_nonzero.default]
  · simp only [bits64, false_and, ite_false, default2, insertEq, BulkKernels.encode_nonzero.default]

#print axioms avx_encode_entry

end BulksketchBridge.AvxEncodeEntry
