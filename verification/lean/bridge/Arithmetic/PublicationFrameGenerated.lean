-- Original checked publication frame declarations.
import Workmeter.Types

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace bulksketch

local notation "fail" => Result.fail

/-- [bulksketch::sketch::api::OutcomeStatus]
    Source: 'src/sketch/api.rs', lines 127:0-136:1 -/
@[discriminant u64]
inductive sketch.api.OutcomeStatus where
| Unset : sketch.api.OutcomeStatus
| Equal : sketch.api.OutcomeStatus
| Decoded : sketch.api.OutcomeStatus
| DegreeExceedsBudget : sketch.api.OutcomeStatus
| InvalidLocator : sketch.api.OutcomeStatus
| NotSplit : sketch.api.OutcomeStatus
| VerificationFailed : sketch.api.OutcomeStatus

/-- [bulksketch::sketch::api::StoredOutcome]
    Source: 'src/sketch/api.rs', lines 140:0-144:1 -/
structure sketch.api.StoredOutcome where
  status : sketch.api.OutcomeStatus
  start : Std.U64
  len : Std.U64

/-- [bulksketch::sketch::api::DecodeReport]
    Source: 'src/sketch/api.rs', lines 66:0-73:1
    Visibility: public -/
structure sketch.api.DecodeReport where
  outcomes : Slice sketch.api.StoredOutcome
  ids : Slice Std.U64
  work : types.WorkUnits
  peak_scratch_bytes : Std.Usize

/-- [bulksketch::sketch::scratch::ResultStorage]
    Source: 'src/sketch/scratch.rs', lines 250:0-253:1 -/
structure sketch.scratch.ResultStorage where
  ids : Slice Std.U64
  outcomes : Slice sketch.api.StoredOutcome

/-- [bulksketch::sketch::api::Publication]
    Source: 'src/sketch/api.rs', lines 232:0-239:1 -/
structure sketch.api.Publication where
  results : sketch.scratch.ResultStorage
  rows : Std.Usize
  written : Std.Usize
  used_ids : Std.Usize
  id_capacity : Std.Usize
  failure : Option types.DecodeError

/-- [bulksketch::sketch::scratch::ScratchLayout]
    Source: 'src/sketch/scratch.rs', lines 56:0-64:1
    Visibility: public -/
structure sketch.scratch.ScratchLayout where
  words : Std.Usize
  raw_products : Std.Usize
  factor_frames : Std.Usize
  result_ids : Std.Usize
  outcomes : Std.Usize
  row_start : Std.Usize
  bytes : Std.Usize

/-- [bulksketch::sketch::api::{impl core::default::Default for bulksketch::sketch::api::OutcomeStatus}::default]:
    Source: 'src/sketch/api.rs', lines 125:29-125:36
    Visibility: public -/
def sketch.api.OutcomeStatus.Insts.CoreDefaultDefault.default
  : Result sketch.api.OutcomeStatus := do
  ok sketch.api.OutcomeStatus.Unset

/-- [bulksketch::sketch::api::{impl core::clone::Clone for bulksketch::sketch::api::StoredOutcome}::clone]:
    Source: 'src/sketch/api.rs', lines 138:9-138:14
    Visibility: public -/
def sketch.api.StoredOutcome.Insts.CoreCloneClone.clone
  (self : sketch.api.StoredOutcome) : Result sketch.api.StoredOutcome := do
  ok self

/-- Trait implementation: [bulksketch::sketch::api::{impl core::clone::Clone for bulksketch::sketch::api::StoredOutcome}]
    Source: 'src/sketch/api.rs', lines 138:9-138:14 -/
@[reducible]
def sketch.api.StoredOutcome.Insts.CoreCloneClone : core.clone.Clone
  sketch.api.StoredOutcome := {
  clone := sketch.api.StoredOutcome.Insts.CoreCloneClone.clone
}

/-- [bulksketch::sketch::api::{impl core::default::Default for bulksketch::sketch::api::StoredOutcome}::default]:
    Source: 'src/sketch/api.rs', lines 138:29-138:36
    Visibility: public -/
def sketch.api.StoredOutcome.Insts.CoreDefaultDefault.default
  : Result sketch.api.StoredOutcome := do
  let os ← sketch.api.OutcomeStatus.Insts.CoreDefaultDefault.default
  ok
    {
      status := os,
      start := (core.default.DefaultU64.default),
      len := (core.default.DefaultU64.default)
    }

/-- [bulksketch::sketch::api::{bulksketch::sketch::api::Publication<'s>}::new]:
    Source: 'src/sketch/api.rs', lines 243:4-257:5 -/
def sketch.api.Publication.new
  (results : sketch.scratch.ResultStorage)
  (layout : sketch.scratch.ScratchLayout) :
  Result (sketch.api.Publication × (sketch.api.Publication →
    sketch.scratch.ResultStorage))
  := do
  let i := Slice.len results.ids
  massert (i >= layout.result_ids)
  let i1 := Slice.len results.outcomes
  massert (i1 >= layout.outcomes)
  let (s, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice sketch.api.StoredOutcome)
      results.outcomes { «end» := layout.outcomes }
  let so ← sketch.api.StoredOutcome.Insts.CoreDefaultDefault.default
  let s1 ←
    core.slice.Slice.fill sketch.api.StoredOutcome.Insts.CoreCloneClone s so
  let s2 := index_mut_back s1
  let back := fun p => p.results
  ok
    ({
       results := { results with outcomes := s2 },
       rows := layout.outcomes,
       written := 0#usize,
       used_ids := 0#usize,
       id_capacity := layout.result_ids,
       failure := none
     }, back)

/-- [bulksketch::sketch::api::{bulksketch::sketch::api::Publication<'s>}::fail]:
    Source: 'src/sketch/api.rs', lines 314:4-318:5 -/
def sketch.api.Publication.fail
  (self : sketch.api.Publication) (error : types.DecodeError) :
  Result (sketch.api.Publication × (sketch.api.Publication →
    sketch.api.Publication))
  := do
  let b := core.option.Option.is_none self.failure
  if b
  then
    let back's := fun self1 => { self with results := self1.results }
    ok ({ self with failure := (some error) }, back's)
  else
    let back's := fun self1 => { self with results := self1.results }
    ok (self, back's)

/-- [bulksketch::sketch::api::{bulksketch::sketch::api::Publication<'s>}::finish]:
    Source: 'src/sketch/api.rs', lines 321:4-339:5 -/
def sketch.api.Publication.finish
  (self : sketch.api.Publication) (work : types.WorkUnits) (peak : Std.Usize) :
  Result ((core.result.Result sketch.api.DecodeReport types.DecodeError) ×
    sketch.api.Publication)
  := do
  match self.failure with
  | none =>
    if self.written = self.rows
    then
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeToUsizeSlice
          sketch.api.StoredOutcome) self.results.outcomes
          { «end» := self.rows }
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
          self.results.ids { «end» := self.used_ids }
      ok (core.result.Result.Ok
        { outcomes := s, ids := s1, work, peak_scratch_bytes := peak }, self)
    else
      let _ ←
        core.fmt.Arguments.from_str (toStr
          "finish requires every row to complete")
      fail panic
  | some error => ok (core.result.Result.Err error, self)

end bulksketch
