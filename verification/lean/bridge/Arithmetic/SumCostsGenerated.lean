-- Exact original sum_costs caller and closures with its checked specialized std slot.
import Arithmetic.WorkScheduleGenerated
import Aeneas.Std.SliceIter

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

noncomputable section

namespace bulksketch

/-- [bulksketch::decode::work::sum_costs::{closure}]
    Source: 'src/decode/work.rs', lines 317:21-317:63 -/
@[reducible]
def decode.work.sum_costs.closure := Unit

/-- [bulksketch::decode::work::sum_costs::{impl core::ops::function::FnMut<(u64, &'_0 bulksketch::decode::work::Charge), core::result::Result<u64, bulksketch::types::DecodeError>> for bulksketch::decode::work::sum_costs::{closure}<'_0>}::call_mut]:
    Source: 'src/decode/work.rs', lines 317:21-317:63 -/
def
  decode.work.sum_costs.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0ChargeResultU64DecodeError.call_mut
  (c : decode.work.sum_costs.closure)
  (tupled_args : (Std.U64 × decode.work.Charge)) :
  Result ((core.result.Result Std.U64 types.DecodeError) ×
    decode.work.sum_costs.closure)
  := do
  let (n, c1) := tupled_args
  let r ← decode.work.WorkScheduleV1.cost c1
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ← decode.work.add n val
    ok (r1, ())
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Std.U64 (core.convert.FromSame types.DecodeError) residual
    ok (r1, ())

/-- [bulksketch::decode::work::sum_costs::{impl core::ops::function::FnOnce<(u64, &'_0 bulksketch::decode::work::Charge), core::result::Result<u64, bulksketch::types::DecodeError>> for bulksketch::decode::work::sum_costs::{closure}<'_0>}::call_once]:
    Source: 'src/decode/work.rs', lines 317:21-317:63 -/
def
  decode.work.sum_costs.closure.Insts.CoreOpsFunctionFnOncePairU64Shared0ChargeResultU64DecodeError.call_once
  (c : decode.work.sum_costs.closure) (p : (Std.U64 × decode.work.Charge)) :
  Result (core.result.Result Std.U64 types.DecodeError)
  := do
  let (r, _) ←
    decode.work.sum_costs.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0ChargeResultU64DecodeError.call_mut
      () p
  ok r

/-- Trait implementation: [bulksketch::decode::work::sum_costs::{impl core::ops::function::FnOnce<(u64, &'_0 bulksketch::decode::work::Charge), core::result::Result<u64, bulksketch::types::DecodeError>> for bulksketch::decode::work::sum_costs::{closure}<'_0>}]
    Source: 'src/decode/work.rs', lines 317:21-317:63 -/
@[reducible]
def
  decode.work.sum_costs.closure.Insts.CoreOpsFunctionFnOncePairU64Shared0ChargeResultU64DecodeError
  : core.ops.function.FnOnce decode.work.sum_costs.closure (Std.U64 ×
  decode.work.Charge) (core.result.Result Std.U64 types.DecodeError) := {
  call_once :=
    decode.work.sum_costs.closure.Insts.CoreOpsFunctionFnOncePairU64Shared0ChargeResultU64DecodeError.call_once
}

/-- Trait implementation: [bulksketch::decode::work::sum_costs::{impl core::ops::function::FnMut<(u64, &'_0 bulksketch::decode::work::Charge), core::result::Result<u64, bulksketch::types::DecodeError>> for bulksketch::decode::work::sum_costs::{closure}<'_0>}]
    Source: 'src/decode/work.rs', lines 317:21-317:63 -/
@[reducible]
def
  decode.work.sum_costs.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0ChargeResultU64DecodeError
  : core.ops.function.FnMut decode.work.sum_costs.closure (Std.U64 ×
  decode.work.Charge) (core.result.Result Std.U64 types.DecodeError) := {
  FnOnceInst :=
    decode.work.sum_costs.closure.Insts.CoreOpsFunctionFnOncePairU64Shared0ChargeResultU64DecodeError
  call_mut :=
    decode.work.sum_costs.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0ChargeResultU64DecodeError.call_mut
}

/-- The specialized shared slice iterator advances once per callback,
including the callback that returns the first error. -/
noncomputable def sumCostsTryFoldFrom :
    List decode.work.Charge → Std.U64 → Nat → decode.work.sum_costs.closure →
      Result ((core.result.Result Std.U64 types.DecodeError) × Nat)
  | [], total, cursor, _ => .ok (.Ok total, cursor)
  | charge :: tail, total, cursor, closure => do
    let (priced, closure) ←
      decode.work.sum_costs.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0ChargeResultU64DecodeError.call_mut
        closure (total, charge)
    match priced with
    | .Err reason => .ok (.Err reason, cursor + 1)
    | .Ok next => sumCostsTryFoldFrom tail next (cursor + 1) closure

/-- Concrete Lean binding of the specialized standard-library slot. -/
noncomputable def decode.work.checked_sum_costs_slice_try_fold
    (iter : core.slice.iter.Iter decode.work.Charge) (total : Std.U64)
    (closure : decode.work.sum_costs.closure) :
    Result ((core.result.Result Std.U64 types.DecodeError) × core.slice.iter.Iter decode.work.Charge) := do
  let (result, cursor) ← sumCostsTryFoldFrom (iter.slice.val.drop iter.i) total iter.i closure
  .ok (result, { iter with i := cursor })

/-- [bulksketch::decode::work::sum_costs]:
    Source: 'src/decode/work.rs', lines 314:0-318:1 -/
def decode.work.sum_costs
  (charges : Slice decode.work.Charge) :
  Result (core.result.Result Std.U64 types.DecodeError)
  := do
  let i ← core.slice.Slice.iter charges
  let (r, _) ←
    bulksketch.decode.work.checked_sum_costs_slice_try_fold i 0#u64 ()
  ok r

end bulksketch
