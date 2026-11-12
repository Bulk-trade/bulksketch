-- Exact original-source declaration projection. Imports are adapted only.
module
public import Workmeter.Funs
public import Arithmetic.SliceKernelTypes
public import Arithmetic.WorkScheduleRuntime
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

/-- [bulksketch::decode::work::number::{closure}]
    Source: 'src/decode/work.rs', lines 303:29-303:63 -/
@[reducible]
def decode.work.number.closure := Unit

/-- [bulksketch::decode::work::{bulksketch::decode::work::WorkScheduleV1}::cost::{closure}]
    Source: 'src/decode/work.rs', lines 140:61-140:95 -/
@[reducible]
def decode.work.WorkScheduleV1.cost.closure := Unit

/-- [bulksketch::decode::work::Charge]
    Source: 'src/decode/work.rs', lines 21:0-99:1 -/
@[discriminant isize]
inductive decode.work.Charge where
| Admission : Std.Usize → decode.work.Charge
| Normalize : Std.Usize → decode.work.Charge
| Compare : Std.Usize → decode.work.Charge
| DirectOne : decode.work.Charge
| DirectTwo : decode.work.Charge
| GuardThree : decode.work.Charge
| NewtonThree : decode.work.Charge
| GuardFour : decode.work.Charge
| NewtonFour : decode.work.Charge
| LeafThree : decode.work.Charge
| LeafFour : decode.work.Charge
| FactorVerification : Std.Usize → decode.work.Charge
| Reconstruct : Std.Usize → decode.work.Charge
| BmStep : Std.Usize → decode.work.Charge
| Candidates : Std.Usize → Std.Usize → decode.work.Charge
| Deflate : Std.Usize → decode.work.Charge
| AffinePreparation : Std.Usize → decode.work.Charge
| AffineEnumeration : Std.Usize → Std.Usize → decode.work.Charge
| AffineSplit : Std.Usize → Std.Usize → decode.work.Charge
| VerifyLfsr : Std.Usize → Std.Usize → Std.Usize → decode.work.Charge
| Table : Std.Usize → decode.work.Charge
| Trace : Std.Usize → decode.work.Charge
| SplitCheck : Std.Usize → decode.work.Charge
| Gcd : Std.Usize → decode.work.Charge
| Divide : Std.Usize → decode.work.Charge
| SplitAssembly : Std.Usize → decode.work.Charge
| Leaf : Std.Usize → decode.work.Charge
| Verify : Std.Usize → Std.Usize → decode.work.Charge
| Canonicalize : Std.Usize → decode.work.Charge

/-- [bulksketch::decode::work::log2_ceil]:
    Source: 'src/decode/work.rs', lines 320:0-326:1 -/
def decode.work.log2_ceil (n : Std.Usize) : Result Std.U64 := do
  if n <= 1#usize
  then ok 0#u64
  else
    let i ← n - 1#usize
    let i1 ← lift (core.num.Usize.leading_zeros i)
    let i2 ← core.num.Usize.BITS - i1
    ok (core.convert.num.FromU64U32.from i2)

/-- [bulksketch::decode::work::mul]:
    Source: 'src/decode/work.rs', lines 310:0-312:1 -/
def decode.work.mul
  (a : Std.U64) (b : Std.U64) :
  Result (core.result.Result Std.U64 types.DecodeError)
  := do
  let o ← lift (U64.checked_mul a b)
  core.option.Option.ok_or o types.DecodeError.WorkLimitExceeded

/-- [bulksketch::decode::work::add]:
    Source: 'src/decode/work.rs', lines 306:0-308:1 -/
def decode.work.add
  (a : Std.U64) (b : Std.U64) :
  Result (core.result.Result Std.U64 types.DecodeError)
  := do
  let o ← lift (U64.checked_add a b)
  core.option.Option.ok_or o types.DecodeError.WorkLimitExceeded

/-- [bulksketch::decode::work::number::{impl core::ops::function::FnOnce<(core::num::error::TryFromIntError,), bulksketch::types::DecodeError> for bulksketch::decode::work::number::{closure}}::call_once]:
    Source: 'src/decode/work.rs', lines 303:29-303:63 -/
def
  decode.work.number.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError.call_once
  (c : decode.work.number.closure)
  (tupled_args : core.num.error.TryFromIntError) :
  Result types.DecodeError
  := do
  ok types.DecodeError.WorkLimitExceeded

/-- Trait implementation: [bulksketch::decode::work::number::{impl core::ops::function::FnOnce<(core::num::error::TryFromIntError,), bulksketch::types::DecodeError> for bulksketch::decode::work::number::{closure}}]
    Source: 'src/decode/work.rs', lines 303:29-303:63 -/
@[reducible]
def
  decode.work.number.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError
  : core.ops.function.FnOnce decode.work.number.closure
  core.num.error.TryFromIntError types.DecodeError := {
  call_once :=
    decode.work.number.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError.call_once
}

/-- [bulksketch::decode::work::number]:
    Source: 'src/decode/work.rs', lines 302:0-304:1 -/
def decode.work.number
  (n : Std.Usize) : Result (core.result.Result Std.U64 types.DecodeError) := do
  let r ← U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from n
  core.result.Result.map_err
    decode.work.number.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError
    r ()

/-- [bulksketch::decode::work::square]:
    Source: 'src/decode/work.rs', lines 298:0-300:1 -/
def decode.work.square
  (n : Std.Usize) : Result (core.result.Result Std.U64 types.DecodeError) := do
  let r ← decode.work.number n
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      decode.work.mul val val1
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Std.U64 (core.convert.FromSame types.DecodeError) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      Std.U64 (core.convert.FromSame types.DecodeError) residual

/-- [bulksketch::decode::work::square_mod]:
    Source: 'src/decode/work.rs', lines 294:0-296:1 -/
def decode.work.square_mod
  (degree : Std.Usize) :
  Result (core.result.Result Std.U64 types.DecodeError)
  := do
  let r ← decode.work.square degree
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ← decode.work.mul 3#u64 val
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r2 ← decode.work.number degree
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let r3 ← decode.work.mul 2#u64 val2
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          decode.work.add val1 val3
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Std.U64 (core.convert.FromSame types.DecodeError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Std.U64 (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Std.U64 (core.convert.FromSame types.DecodeError) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      Std.U64 (core.convert.FromSame types.DecodeError) residual

/-- [bulksketch::decode::work::{bulksketch::decode::work::WorkScheduleV1}::cost::{impl core::ops::function::FnOnce<(core::num::error::TryFromIntError,), bulksketch::types::DecodeError> for bulksketch::decode::work::{bulksketch::decode::work::WorkScheduleV1}::cost::{closure}}::call_once]:
    Source: 'src/decode/work.rs', lines 140:61-140:95 -/
def
  decode.work.WorkScheduleV1.cost.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError.call_once
  (c : decode.work.WorkScheduleV1.cost.closure)
  (tupled_args : core.num.error.TryFromIntError) :
  Result types.DecodeError
  := do
  ok types.DecodeError.WorkLimitExceeded

/-- Trait implementation: [bulksketch::decode::work::{bulksketch::decode::work::WorkScheduleV1}::cost::{impl core::ops::function::FnOnce<(core::num::error::TryFromIntError,), bulksketch::types::DecodeError> for bulksketch::decode::work::{bulksketch::decode::work::WorkScheduleV1}::cost::{closure}}]
    Source: 'src/decode/work.rs', lines 140:61-140:95 -/
@[reducible]
def
  decode.work.WorkScheduleV1.cost.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError
  : core.ops.function.FnOnce decode.work.WorkScheduleV1.cost.closure
  core.num.error.TryFromIntError types.DecodeError := {
  call_once :=
    decode.work.WorkScheduleV1.cost.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError.call_once
}

/-- [bulksketch::decode::work::{bulksketch::decode::work::WorkScheduleV1}::cost]:
    Source: 'src/decode/work.rs', lines 108:4-197:5 -/
def decode.work.WorkScheduleV1.cost
  (charge : decode.work.Charge) :
  Result (core.result.Result types.WorkUnits types.DecodeError)
  := do
  match charge with
  | decode.work.Charge.Admission rows =>
    let r ← decode.work.number rows
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ← decode.work.add 1#u64 val
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        ok (core.result.Result.Ok val1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | decode.work.Charge.Normalize inputs =>
    let r ← decode.work.number inputs
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i ← decode.work.log2_ceil inputs
      let r1 ← decode.work.add i 3#u64
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r2 ← decode.work.mul val val1
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          ok (core.result.Result.Ok val2)
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            types.WorkUnits (core.convert.FromSame types.DecodeError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | decode.work.Charge.Compare capacity =>
    let r ← decode.work.number capacity
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ← decode.work.add val 1#u64
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        ok (core.result.Result.Ok val1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | decode.work.Charge.DirectOne => ok (core.result.Result.Ok 1#u64)
  | decode.work.Charge.DirectTwo => ok (core.result.Result.Ok 168#u64)
  | decode.work.Charge.GuardThree => ok (core.result.Result.Ok 48#u64)
  | decode.work.Charge.NewtonThree => ok (core.result.Result.Ok 144#u64)
  | decode.work.Charge.GuardFour => ok (core.result.Result.Ok 80#u64)
  | decode.work.Charge.NewtonFour => ok (core.result.Result.Ok 160#u64)
  | decode.work.Charge.LeafThree => ok (core.result.Result.Ok 640#u64)
  | decode.work.Charge.LeafFour => ok (core.result.Result.Ok 2048#u64)
  | decode.work.Charge.FactorVerification degree =>
    let r ← decode.work.square degree
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ← decode.work.mul 2#u64 val
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r2 ← decode.work.number degree
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let r3 ← decode.work.mul 4#u64 val2
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let r4 ← decode.work.add val1 val3
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val4 =>
              let r5 ← decode.work.add val4 1#u64
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue val5 =>
                ok (core.result.Result.Ok val5)
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  types.WorkUnits (core.convert.FromSame types.DecodeError)
                  residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                types.WorkUnits (core.convert.FromSame types.DecodeError)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              types.WorkUnits (core.convert.FromSame types.DecodeError)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            types.WorkUnits (core.convert.FromSame types.DecodeError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | decode.work.Charge.Reconstruct capacity =>
    let r ← decode.work.number capacity
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ← decode.work.mul 3#u64 val
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        ok (core.result.Result.Ok val1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | decode.work.Charge.BmStep budget =>
    let r ← decode.work.number budget
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ← decode.work.add val 1#u64
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r2 ← decode.work.mul 6#u64 val1
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let r3 ← decode.work.add val2 128#u64
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            ok (core.result.Result.Ok val3)
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              types.WorkUnits (core.convert.FromSame types.DecodeError)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            types.WorkUnits (core.convert.FromSame types.DecodeError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | decode.work.Charge.Candidates degree inputs =>
    let r ← decode.work.number inputs
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ← decode.work.mul 2#u64 val
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r2 ← decode.work.number degree
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let r3 ← decode.work.add val2 1#u64
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let r4 ← decode.work.mul val1 val3
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val4 =>
              ok (core.result.Result.Ok val4)
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                types.WorkUnits (core.convert.FromSame types.DecodeError)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              types.WorkUnits (core.convert.FromSame types.DecodeError)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            types.WorkUnits (core.convert.FromSame types.DecodeError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | decode.work.Charge.Deflate degree =>
    let r ← decode.work.number degree
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ← decode.work.mul 2#u64 val
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let r2 ← decode.work.add val2 1#u64
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let r3 ← decode.work.mul val1 val3
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val4 =>
              ok (core.result.Result.Ok val4)
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                types.WorkUnits (core.convert.FromSame types.DecodeError)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              types.WorkUnits (core.convert.FromSame types.DecodeError)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            types.WorkUnits (core.convert.FromSame types.DecodeError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | decode.work.Charge.AffinePreparation degree =>
    let r ← decode.work.number degree
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ← decode.work.mul val val
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r2 ← decode.work.mul val1 val
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let r3 ← decode.work.mul 5#u64 val2
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let r4 ← decode.work.mul 16#u64 val1
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val4 =>
              let r5 ← decode.work.add val3 val4
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue val5 =>
                let r6 ← decode.work.mul 327#u64 val
                let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                match cf6 with
                | core.ops.control_flow.ControlFlow.Continue val6 =>
                  let r7 ← decode.work.add val6 16900#u64
                  let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                  match cf7 with
                  | core.ops.control_flow.ControlFlow.Continue val7 =>
                    let r8 ← decode.work.add val5 val7
                    let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r8
                    match cf8 with
                    | core.ops.control_flow.ControlFlow.Continue val8 =>
                      ok (core.result.Result.Ok val8)
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        types.WorkUnits (core.convert.FromSame
                        types.DecodeError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      types.WorkUnits (core.convert.FromSame types.DecodeError)
                      residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    types.WorkUnits (core.convert.FromSame types.DecodeError)
                    residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  types.WorkUnits (core.convert.FromSame types.DecodeError)
                  residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                types.WorkUnits (core.convert.FromSame types.DecodeError)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              types.WorkUnits (core.convert.FromSame types.DecodeError)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            types.WorkUnits (core.convert.FromSame types.DecodeError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | decode.work.Charge.AffineEnumeration degree rank =>
    let r ← core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from rank
    let r1 ←
      core.result.Result.map_err
        decode.work.WorkScheduleV1.cost.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError
        r ()
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let o ← core.num.U64.checked_shl 1#u64 val
      let r2 ← core.option.Option.ok_or o types.DecodeError.WorkLimitExceeded
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r3 ← decode.work.mul 2#u64 val1
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let r4 ← decode.work.number degree
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let r5 ← decode.work.add val3 2#u64
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val4 =>
              let r6 ← decode.work.mul val2 val4
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue val5 =>
                let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r4
                match cf6 with
                | core.ops.control_flow.ControlFlow.Continue val6 =>
                  let r7 ← decode.work.add val6 1#u64
                  let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                  match cf7 with
                  | core.ops.control_flow.ControlFlow.Continue val7 =>
                    let r8 ← decode.work.add val5 val7
                    let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r8
                    match cf8 with
                    | core.ops.control_flow.ControlFlow.Continue val8 =>
                      ok (core.result.Result.Ok val8)
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        types.WorkUnits (core.convert.FromSame
                        types.DecodeError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      types.WorkUnits (core.convert.FromSame types.DecodeError)
                      residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    types.WorkUnits (core.convert.FromSame types.DecodeError)
                    residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  types.WorkUnits (core.convert.FromSame types.DecodeError)
                  residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                types.WorkUnits (core.convert.FromSame types.DecodeError)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              types.WorkUnits (core.convert.FromSame types.DecodeError)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            types.WorkUnits (core.convert.FromSame types.DecodeError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | decode.work.Charge.AffineSplit degree rank =>
    let r ← decode.work.number degree
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ← decode.work.number rank
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r2 ← decode.work.square_mod degree
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let r3 ← decode.work.mul 3#u64 val
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let r4 ← decode.work.add val3 3#u64
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val4 =>
              let r5 ← decode.work.add val2 val4
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue val5 =>
                let r6 ← decode.work.mul val1 val5
                let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                match cf6 with
                | core.ops.control_flow.ControlFlow.Continue val6 =>
                  let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r3
                  match cf7 with
                  | core.ops.control_flow.ControlFlow.Continue val7 =>
                    let r7 ← decode.work.add val7 1#u64
                    let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r7
                    match cf8 with
                    | core.ops.control_flow.ControlFlow.Continue val8 =>
                      let r8 ← decode.work.add val6 val8
                      let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r8
                      match cf9 with
                      | core.ops.control_flow.ControlFlow.Continue val9 =>
                        ok (core.result.Result.Ok val9)
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                          types.WorkUnits (core.convert.FromSame
                          types.DecodeError) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        types.WorkUnits (core.convert.FromSame
                        types.DecodeError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      types.WorkUnits (core.convert.FromSame types.DecodeError)
                      residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    types.WorkUnits (core.convert.FromSame types.DecodeError)
                    residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  types.WorkUnits (core.convert.FromSame types.DecodeError)
                  residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                types.WorkUnits (core.convert.FromSame types.DecodeError)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              types.WorkUnits (core.convert.FromSame types.DecodeError)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            types.WorkUnits (core.convert.FromSame types.DecodeError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | decode.work.Charge.VerifyLfsr capacity output_budget degree =>
    let r ← decode.work.number degree
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ← decode.work.mul 3#u64 val
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r2 ← decode.work.add val1 4#u64
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let r3 ← decode.work.number capacity
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let r4 ← decode.work.mul val2 val3
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val4 =>
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue val5 =>
                let r5 ← decode.work.number output_budget
                let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r5
                match cf6 with
                | core.ops.control_flow.ControlFlow.Continue val6 =>
                  let r6 ← decode.work.add val6 3#u64
                  let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r6
                  match cf7 with
                  | core.ops.control_flow.ControlFlow.Continue val7 =>
                    let r7 ← decode.work.add val5 val7
                    let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r7
                    match cf8 with
                    | core.ops.control_flow.ControlFlow.Continue val8 =>
                      let r8 ← decode.work.add val4 val8
                      let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r8
                      match cf9 with
                      | core.ops.control_flow.ControlFlow.Continue val9 =>
                        ok (core.result.Result.Ok val9)
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                          types.WorkUnits (core.convert.FromSame
                          types.DecodeError) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        types.WorkUnits (core.convert.FromSame
                        types.DecodeError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      types.WorkUnits (core.convert.FromSame types.DecodeError)
                      residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    types.WorkUnits (core.convert.FromSame types.DecodeError)
                    residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  types.WorkUnits (core.convert.FromSame types.DecodeError)
                  residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                types.WorkUnits (core.convert.FromSame types.DecodeError)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              types.WorkUnits (core.convert.FromSame types.DecodeError)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            types.WorkUnits (core.convert.FromSame types.DecodeError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | decode.work.Charge.Table degree =>
    let r ← decode.work.square degree
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ← decode.work.mul 8#u64 val
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r2 ← decode.work.number degree
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let r3 ← decode.work.mul 2#u64 val2
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let r4 ← decode.work.add val1 val3
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val4 =>
              ok (core.result.Result.Ok val4)
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                types.WorkUnits (core.convert.FromSame types.DecodeError)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              types.WorkUnits (core.convert.FromSame types.DecodeError)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            types.WorkUnits (core.convert.FromSame types.DecodeError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | decode.work.Charge.Trace degree =>
    let r ← decode.work.square_mod degree
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ← decode.work.add val 2#u64
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r2 ← decode.work.mul 63#u64 val1
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          ok (core.result.Result.Ok val2)
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            types.WorkUnits (core.convert.FromSame types.DecodeError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | decode.work.Charge.SplitCheck degree =>
    let r ← decode.work.square_mod degree
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ← decode.work.number degree
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r2 ← decode.work.add val1 1#u64
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let r3 ← decode.work.add val val2
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            ok (core.result.Result.Ok val3)
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              types.WorkUnits (core.convert.FromSame types.DecodeError)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            types.WorkUnits (core.convert.FromSame types.DecodeError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | decode.work.Charge.Gcd degree =>
    let r ← decode.work.number degree
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ← decode.work.add val 1#u64
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r2 ← decode.work.mul val1 val1
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let r3 ← decode.work.mul 8#u64 val2
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let r4 ← decode.work.mul 128#u64 val1
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val4 =>
              let r5 ← decode.work.add val3 val4
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue val5 =>
                ok (core.result.Result.Ok val5)
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  types.WorkUnits (core.convert.FromSame types.DecodeError)
                  residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                types.WorkUnits (core.convert.FromSame types.DecodeError)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              types.WorkUnits (core.convert.FromSame types.DecodeError)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            types.WorkUnits (core.convert.FromSame types.DecodeError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | decode.work.Charge.Divide degree =>
    let r ← decode.work.number degree
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ← decode.work.add val 1#u64
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r2 ← decode.work.mul val1 val1
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let r3 ← decode.work.mul 4#u64 val2
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let r4 ← decode.work.add val3 128#u64
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val4 =>
              ok (core.result.Result.Ok val4)
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                types.WorkUnits (core.convert.FromSame types.DecodeError)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              types.WorkUnits (core.convert.FromSame types.DecodeError)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            types.WorkUnits (core.convert.FromSame types.DecodeError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | decode.work.Charge.SplitAssembly degree =>
    let r ← decode.work.number degree
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ← decode.work.add val 1#u64
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r2 ← decode.work.mul 4#u64 val1
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          ok (core.result.Result.Ok val2)
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            types.WorkUnits (core.convert.FromSame types.DecodeError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | decode.work.Charge.Leaf degree =>
    match degree.val with
    | 0 => ok (core.result.Result.Ok 0#u64)
    | 1 => ok (core.result.Result.Ok 1#u64)
    | 2 => ok (core.result.Result.Ok 160#u64)
    | _ => fail panic
  | decode.work.Charge.Verify capacity output_budget =>
    let r ← decode.work.number output_budget
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ← decode.work.mul 2#u64 val
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r2 ← decode.work.add val1 3#u64
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let r3 ← decode.work.number capacity
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let r4 ← decode.work.mul val2 val3
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val4 =>
              let r5 ← decode.work.add val 1#u64
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue val5 =>
                let r6 ← decode.work.add val4 val5
                let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                match cf6 with
                | core.ops.control_flow.ControlFlow.Continue val6 =>
                  ok (core.result.Result.Ok val6)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    types.WorkUnits (core.convert.FromSame types.DecodeError)
                    residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  types.WorkUnits (core.convert.FromSame types.DecodeError)
                  residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                types.WorkUnits (core.convert.FromSame types.DecodeError)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              types.WorkUnits (core.convert.FromSame types.DecodeError)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            types.WorkUnits (core.convert.FromSame types.DecodeError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | decode.work.Charge.Canonicalize ids =>
    let r ← decode.work.number ids
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i ← decode.work.log2_ceil ids
      let r1 ← decode.work.add i 1#u64
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r2 ← decode.work.mul val val1
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          ok (core.result.Result.Ok val2)
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            types.WorkUnits (core.convert.FromSame types.DecodeError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::charge]:
    Source: 'src/decode/stages.rs', lines 163:4-165:5 -/
def decode.stages.Execution.charge
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (meter : types.WorkMeter) (operation : decode.work.Charge) :
  Result ((core.result.Result Unit types.DecodeError) × types.WorkMeter)
  := do
  let r ← decode.work.WorkScheduleV1.cost operation
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    types.WorkMeter.charge meter val
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame types.DecodeError) residual
    ok (r1, meter)

end bulksketch
