-- Original checked decode-execution variant dispatch.
import Arithmetic.RowConfigurationGenerated
import Arithmetic.AvxLinearEntryGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace bulksketch

/-- [bulksketch::backend::x86_pclmul::Pclmul]
    Source: 'src/backend/x86_pclmul.rs', lines 19:0-19:25 -/
@[reducible]
def backend.x86_pclmul.Pclmul := Unit

/-- [bulksketch::backend::x86_vpclmul512::Vpclmul512]
    Source: 'src/backend/x86_vpclmul512.rs', lines 28:0-28:29 -/
@[reducible]
def backend.x86_vpclmul512.Vpclmul512 := Unit

/-- [bulksketch::decode::probe::Probe]
    Source: 'src/decode/probe.rs', lines 18:0-29:1 -/
structure decode.probe.Probe where
  budget : decode.row.RowBudget
  next : Option types.Stage
  count : Std.Usize
  pair : Bool

/-- [bulksketch::types::BackendId]
    Source: 'src/types.rs', lines 52:0-61:1
    Visibility: public -/
@[discriminant isize]
inductive types.BackendId where
| Portable : types.BackendId
| Pclmul : types.BackendId
| Vpclmul256 : types.BackendId
| Vpclmul512 : types.BackendId

/-- [bulksketch::sketch::dispatch::DecodeExecution]
    Source: 'src/sketch/dispatch.rs', lines 119:0-126:1 -/
@[discriminant isize]
inductive sketch.dispatch.DecodeExecution (F : Type _) where
| Probe :
  decode.probe.Probe →
  types.BackendId →
  sketch.dispatch.DecodeExecution F
| Portable :
  decode.stages.Execution F backend.portable.Portable →
  sketch.dispatch.DecodeExecution F
| Pclmul :
  decode.stages.Execution F backend.x86_pclmul.Pclmul →
  sketch.dispatch.DecodeExecution F
| Vpclmul512 :
  decode.stages.Execution F backend.x86_vpclmul512.Vpclmul512 →
  sketch.dispatch.DecodeExecution F

end bulksketch

namespace Aeneas.Std.RowDispatchRuntime

open bulksketch.backend.contract bulksketch.backend.portable
open bulksketch.backend.x86_pclmul bulksketch.backend.x86_vpclmul512
open bulksketch.decode.probe bulksketch.decode.row bulksketch.types

structure Dictionaries where
  portable : {F : Type} → bulksketch.field.BinaryField F → BulkKernels Portable F
  pclmul : {F : Type} → bulksketch.field.BinaryField F → BulkKernels Pclmul F
  vpclmul512 : {F : Type} → bulksketch.field.BinaryField F → BulkKernels Vpclmul512 F

abbrev ProbeRun :=
  {F : Type} → bulksketch.field.BinaryField F → BackendId → Probe →
    Slice U64 → Slice U64 → Slice U64 → WorkMeter →
    Result (core.result.Result RowProgress DecodeError × Probe × Slice U64 × Slice U64 × WorkMeter)

end Aeneas.Std.RowDispatchRuntime

namespace bulksketch

variable (dictionaries : RowDispatchRuntime.Dictionaries)
variable (calls : RootRunRuntime.OtherCallees) (division : DenseDivisionRuntime.DivRem)
variable (canonicalize : ExecutionDriverRuntime.Canonicalize) (probeRun : RowDispatchRuntime.ProbeRun)

local notation "backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels" => dictionaries.portable
local notation "backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels" => dictionaries.pclmul
local notation "backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels" => dictionaries.vpclmul512
local notation "decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.run_next" =>
  (decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.run_next calls division canonicalize)
local notation "sketch.dispatch.run_probe" => probeRun

/-- [bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::next_stage]:
    Source: 'src/decode/probe.rs', lines 47:4-49:5 -/
def decode.probe.Probe.next_stage
  (self : decode.probe.Probe) : Result (Option types.Stage) := do
  ok self.next

/-- [bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::count]:
    Source: 'src/decode/probe.rs', lines 50:4-52:5 -/
def decode.probe.Probe.impl.count
  (self : decode.probe.Probe) : Result Std.Usize := do
  ok self.count

/-- [bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::reject]:
    Source: 'src/decode/probe.rs', lines 58:4-66:5 -/
def decode.probe.Probe.reject
  (self : decode.probe.Probe) (capacity : Std.Usize) :
  Result decode.probe.Probe
  := do
  if self.pair
  then
    ok
      { self with next := (some types.Stage.Reconstruction), count := 0#usize }
  else
    if capacity >= 2#usize
    then
      if self.budget.nonzero >= 2#usize
      then
        ok
          {
            self
              with
              next := (some types.Stage.DirectTwo),
              count := 0#usize,
              pair := true
          }
      else
        ok
          {
            self
              with
              next := (some types.Stage.Reconstruction), count := 0#usize
          }
    else
      ok
        { self with next := (some types.Stage.Reconstruction), count := 0#usize
        }

/-- [bulksketch::sketch::dispatch::{bulksketch::sketch::dispatch::DecodeExecution<F>}::enable_v3]:
    Source: 'src/sketch/dispatch.rs', lines 129:4-138:5 -/
def sketch.dispatch.DecodeExecution.enable_v3
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (self : sketch.dispatch.DecodeExecution F) :
  Result (sketch.dispatch.DecodeExecution F)
  := do
  match self with
  | sketch.dispatch.DecodeExecution.Probe _ _ => ok self
  | sketch.dispatch.DecodeExecution.Portable row =>
    let row1 ←
      decode.stages.Execution.enable_v3 fieldBinaryFieldInst
        (backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels
        fieldBinaryFieldInst) row
    ok (sketch.dispatch.DecodeExecution.Portable row1)
  | sketch.dispatch.DecodeExecution.Pclmul row =>
    let row1 ←
      decode.stages.Execution.enable_v3 fieldBinaryFieldInst
        (backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels
        fieldBinaryFieldInst) row
    ok (sketch.dispatch.DecodeExecution.Pclmul row1)
  | sketch.dispatch.DecodeExecution.Vpclmul512 row =>
    let row1 ←
      decode.stages.Execution.enable_v3 fieldBinaryFieldInst
        (backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels
        fieldBinaryFieldInst) row
    ok (sketch.dispatch.DecodeExecution.Vpclmul512 row1)

/-- [bulksketch::sketch::dispatch::{bulksketch::sketch::dispatch::DecodeExecution<F>}::start_degrees]:
    Source: 'src/sketch/dispatch.rs', lines 140:4-149:5 -/
def sketch.dispatch.DecodeExecution.start_degrees
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (self : sketch.dispatch.DecodeExecution F) (capacity : Std.Usize) :
  Result (sketch.dispatch.DecodeExecution F)
  := do
  match self with
  | sketch.dispatch.DecodeExecution.Probe _ _ => ok self
  | sketch.dispatch.DecodeExecution.Portable row =>
    let row1 ←
      decode.stages.Execution.start_degrees fieldBinaryFieldInst
        (backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels
        fieldBinaryFieldInst) row capacity
    ok (sketch.dispatch.DecodeExecution.Portable row1)
  | sketch.dispatch.DecodeExecution.Pclmul row =>
    let row1 ←
      decode.stages.Execution.start_degrees fieldBinaryFieldInst
        (backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels
        fieldBinaryFieldInst) row capacity
    ok (sketch.dispatch.DecodeExecution.Pclmul row1)
  | sketch.dispatch.DecodeExecution.Vpclmul512 row =>
    let row1 ←
      decode.stages.Execution.start_degrees fieldBinaryFieldInst
        (backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels
        fieldBinaryFieldInst) row capacity
    ok (sketch.dispatch.DecodeExecution.Vpclmul512 row1)

/-- [bulksketch::sketch::dispatch::{bulksketch::sketch::dispatch::DecodeExecution<F>}::verification_count]:
    Source: 'src/sketch/dispatch.rs', lines 150:4-159:5 -/
def sketch.dispatch.DecodeExecution.verification_count
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (self : sketch.dispatch.DecodeExecution F) :
  Result Std.Usize
  := do
  match self with
  | sketch.dispatch.DecodeExecution.Probe probe _ =>
    decode.probe.Probe.impl.count probe
  | sketch.dispatch.DecodeExecution.Portable row =>
    decode.stages.Execution.verification_count fieldBinaryFieldInst
      (backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels
      fieldBinaryFieldInst) row
  | sketch.dispatch.DecodeExecution.Pclmul row =>
    decode.stages.Execution.verification_count fieldBinaryFieldInst
      (backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels
      fieldBinaryFieldInst) row
  | sketch.dispatch.DecodeExecution.Vpclmul512 row =>
    decode.stages.Execution.verification_count fieldBinaryFieldInst
      (backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels
      fieldBinaryFieldInst) row

/-- [bulksketch::sketch::dispatch::{bulksketch::sketch::dispatch::DecodeExecution<F>}::reject_upper]:
    Source: 'src/sketch/dispatch.rs', lines 160:4-169:5 -/
def sketch.dispatch.DecodeExecution.reject_upper
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (self : sketch.dispatch.DecodeExecution F) (capacity : Std.Usize) :
  Result (sketch.dispatch.DecodeExecution F)
  := do
  match self with
  | sketch.dispatch.DecodeExecution.Probe probe bi =>
    let probe1 ← decode.probe.Probe.reject probe capacity
    ok (sketch.dispatch.DecodeExecution.Probe probe1 bi)
  | sketch.dispatch.DecodeExecution.Portable row =>
    let row1 ←
      decode.stages.Execution.reject_upper fieldBinaryFieldInst
        (backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels
        fieldBinaryFieldInst) row capacity
    ok (sketch.dispatch.DecodeExecution.Portable row1)
  | sketch.dispatch.DecodeExecution.Pclmul row =>
    let row1 ←
      decode.stages.Execution.reject_upper fieldBinaryFieldInst
        (backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels
        fieldBinaryFieldInst) row capacity
    ok (sketch.dispatch.DecodeExecution.Pclmul row1)
  | sketch.dispatch.DecodeExecution.Vpclmul512 row =>
    let row1 ←
      decode.stages.Execution.reject_upper fieldBinaryFieldInst
        (backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels
        fieldBinaryFieldInst) row capacity
    ok (sketch.dispatch.DecodeExecution.Vpclmul512 row1)

/-- [bulksketch::sketch::dispatch::{bulksketch::sketch::dispatch::DecodeExecution<F>}::next_stage]:
    Source: 'src/sketch/dispatch.rs', lines 188:4-197:5 -/
def sketch.dispatch.DecodeExecution.next_stage
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (self : sketch.dispatch.DecodeExecution F) :
  Result (Option types.Stage)
  := do
  match self with
  | sketch.dispatch.DecodeExecution.Probe probe _ =>
    decode.probe.Probe.next_stage probe
  | sketch.dispatch.DecodeExecution.Portable row =>
    decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.next_stage
      fieldBinaryFieldInst
      (backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels
      fieldBinaryFieldInst) row
  | sketch.dispatch.DecodeExecution.Pclmul row =>
    decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.next_stage
      fieldBinaryFieldInst
      (backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels
      fieldBinaryFieldInst) row
  | sketch.dispatch.DecodeExecution.Vpclmul512 row =>
    decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.next_stage
      fieldBinaryFieldInst
      (backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels
      fieldBinaryFieldInst) row

/-- [bulksketch::sketch::dispatch::{bulksketch::sketch::dispatch::DecodeExecution<F>}::run_next]:
    Source: 'src/sketch/dispatch.rs', lines 199:4-220:5 -/
def sketch.dispatch.DecodeExecution.run_next
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (self : sketch.dispatch.DecodeExecution F) (input : decode.row.RowInput)
  (workspace : decode.scratch.RowWorkspace) (meter : types.WorkMeter) :
  Result ((core.result.Result decode.row.RowProgress types.DecodeError) ×
    (sketch.dispatch.DecodeExecution F) × decode.scratch.RowWorkspace ×
    (decode.scratch.RowWorkspace → decode.scratch.RowWorkspace) ×
    types.WorkMeter)
  := do
  match self with
  | sketch.dispatch.DecodeExecution.Probe probe backend =>
    let (r, probe1, s, s1, meter1) ←
      sketch.dispatch.run_probe fieldBinaryFieldInst backend probe
        input.difference workspace.verification workspace.roots meter
    ok (r, sketch.dispatch.DecodeExecution.Probe probe1 backend,
      { workspace with verification := s, roots := s1 },
      fun workspace1 => workspace1, meter1)
  | sketch.dispatch.DecodeExecution.Portable row =>
    let (r, row1, workspace1, run_next_back, meter1) ←
      decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.run_next
        fieldBinaryFieldInst
        (backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels
        fieldBinaryFieldInst) row input workspace meter
    ok (r, sketch.dispatch.DecodeExecution.Portable row1, workspace1,
      run_next_back, meter1)
  | sketch.dispatch.DecodeExecution.Pclmul row =>
    let (r, row1, workspace1, run_next_back, meter1) ←
      decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.run_next
        fieldBinaryFieldInst
        (backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels
        fieldBinaryFieldInst) row input workspace meter
    ok (r, sketch.dispatch.DecodeExecution.Pclmul row1, workspace1,
      run_next_back, meter1)
  | sketch.dispatch.DecodeExecution.Vpclmul512 row =>
    let (r, row1, workspace1, run_next_back, meter1) ←
      decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.run_next
        fieldBinaryFieldInst
        (backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels
        fieldBinaryFieldInst) row input workspace meter
    ok (r, sketch.dispatch.DecodeExecution.Vpclmul512 row1, workspace1,
      run_next_back, meter1)

end bulksketch
