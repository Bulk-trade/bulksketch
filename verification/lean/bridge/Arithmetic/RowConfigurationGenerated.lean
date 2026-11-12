-- Exact original row initialization and configuration declarations.
import Arithmetic.ExecutionDriverGenerated
import Arithmetic.DegreeProbeGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false

namespace bulksketch

local notation "core.option.Option.Insts.CoreCmpPartialEqOption.eq" => ExecutionDriverRuntime.optionEq

/-- [bulksketch::decode::roots::{impl core::default::Default for bulksketch::decode::roots::Roots}::default]:
    Source: 'src/decode/roots.rs', lines 17:16-17:23
    Visibility: public -/
def decode.roots.Roots.Insts.CoreDefaultDefault.default
  : Result decode.roots.Roots := do
  let b ← core.default.DefaultBool.default
  ok
    {
      pending := (core.default.DefaultUsize.default),
      stride := (core.default.DefaultUsize.default),
      degree := (core.default.DefaultUsize.default),
      direction := (core.default.DefaultU32.default),
      checked := b,
      trace_len := (core.default.DefaultUsize.default),
      gcd_len := (core.default.DefaultUsize.default),
      count := (core.default.DefaultUsize.default),
      attempts := (core.default.DefaultUsize.default),
      gcd_degree := (core.default.DefaultUsize.default),
      splitter_seed := (core.default.DefaultU64.default),
      v3 := b,
      closed_form := b,
      solved_count := (core.default.DefaultUsize.default),
      affine := b,
      affine_ready := b,
      affine_base := (core.default.DefaultU64.default),
      affine_rank := (core.default.DefaultUsize.default)
    }

/-- [bulksketch::decode::stages::{impl bulksketch::decode::row::RowDecoder<F, K, bulksketch::decode::stages::Execution<F, K>> for bulksketch::decode::stages::BinaryDecoder}::begin]:
    Source: 'src/decode/stages.rs', lines 56:4-75:5 -/
def
  decode.stages.BinaryDecoder.Insts.BulksketchDecodeRowRowDecoderFKExecution.begin
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (budget : decode.row.RowBudget) :
  Result (decode.stages.Execution F K)
  := do
  let r ← decode.roots.Roots.Insts.CoreDefaultDefault.default
  ok
    {
      budget,
      state := (decode.stages.State.Running types.Stage.Reconstruction),
      degree := 0#usize,
      hits := 0#usize,
      roots := r,
      v3 := false,
      degree_probe := none,
      marker := ()
    }

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::set_splitter_seed]:
    Source: 'src/decode/stages.rs', lines 159:4-161:5 -/
def decode.stages.Execution.set_splitter_seed
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (self : decode.stages.Execution F K) (seed : Std.U64) :
  Result (decode.stages.Execution F K)
  := do
  let r ← decode.roots.Roots.set_splitter_seed self.roots seed
  ok { self with roots := r }

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::restart]:
    Source: 'src/decode/stages.rs', lines 92:4-95:5 -/
def decode.stages.Execution.restart
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (self : decode.stages.Execution F K) (budget : decode.row.RowBudget)
  (seed : Std.U64) :
  Result (decode.stages.Execution F K)
  := do
  let self1 ←
    decode.stages.BinaryDecoder.Insts.BulksketchDecodeRowRowDecoderFKExecution.begin
      fieldBinaryFieldInst backendcontractBulkKernelsInst budget
  decode.stages.Execution.set_splitter_seed fieldBinaryFieldInst
    backendcontractBulkKernelsInst self1 seed

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::enable_v3]:
    Source: 'src/decode/stages.rs', lines 97:4-103:5 -/
def decode.stages.Execution.enable_v3
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (self : decode.stages.Execution F K) :
  Result (decode.stages.Execution F K)
  := do
  let r ← decode.roots.Roots.enable_v3 self.roots
  let i ← fieldBinaryFieldInst.BITS
  if i = 64#u32
  then
    let r1 ← decode.roots.Roots.enable_closed_form r
    ok { self with roots := r1, v3 := true }
  else ok { self with roots := r, v3 := true }

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::start_degrees]:
    Source: 'src/decode/stages.rs', lines 106:4-113:5 -/
def decode.stages.Execution.start_degrees
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (self : decode.stages.Execution F K) (capacity : Std.Usize) :
  Result (decode.stages.Execution F K)
  := do
  if self.v3
  then
    let i ← fieldBinaryFieldInst.BITS
    if i = 64#u32
    then
      let o ← decode.degree_probe.DegreeProbe.new self.budget capacity
      match o with
      | none => ok { self with degree_probe := none }
      | some probe =>
        let o1 ← decode.degree_probe.DegreeProbe.next_stage probe
        let s ← core.option.Option.expect o1 (toStr "new degree probe")
        ok
          {
            self
              with
              state := (decode.stages.State.Running s), degree_probe := o
          }
    else ok self
  else ok self

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::verification_count]:
    Source: 'src/decode/stages.rs', lines 115:4-117:5 -/
def decode.stages.Execution.verification_count
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (self : decode.stages.Execution F K) :
  Result Std.Usize
  := do
  ok self.roots.count

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::reject_upper]:
    Source: 'src/decode/stages.rs', lines 120:4-131:5 -/
def decode.stages.Execution.reject_upper
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (self : decode.stages.Execution F K) (capacity : Std.Usize) :
  Result (decode.stages.Execution F K)
  := do
  match self.degree_probe with
  | none =>
    ok
      {
        self
          with
          state :=
            (decode.stages.State.Failed types.DecodeFailure.InvalidLocator)
      }
  | some probe =>
    let probe1 ←
      decode.degree_probe.DegreeProbe.reject probe capacity self.budget
    let o ← decode.degree_probe.DegreeProbe.next_stage probe1
    let s ← core.option.Option.expect o (toStr "probe fallback")
    let b ←
      core.option.Option.Insts.CoreCmpPartialEqOption.eq
        types.Stage.Insts.CoreCmpPartialEqStage o (some
        types.Stage.Reconstruction)
    if b
    then
      ok
        {
          self
            with
            state := (decode.stages.State.Running s),
            roots := { self.roots with count := 0#usize },
            degree_probe := none
        }
    else
      ok
        {
          self
            with
            state := (decode.stages.State.Running s),
            roots := { self.roots with count := 0#usize },
            degree_probe := (some probe1)
        }

end bulksketch
