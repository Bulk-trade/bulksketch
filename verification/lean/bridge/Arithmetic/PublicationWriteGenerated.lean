-- Verbatim Publication::write declarations from the checked original capture.
import Arithmetic.PublicationWriteRuntime

open Aeneas Aeneas.Std Result Error ControlFlow
set_option linter.dupNamespace false
set_option linter.unusedVariables false

noncomputable section

namespace bulksketch

local notation "core.slice.Slice.first" => PublicationWriteRuntime.first
local notation "core.option.Option.and_then" => PublicationWriteRuntime.andThen
local notation "core.slice.Slice.windows" => CanonicalizeRuntime.windows
local notation "core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice" => (fun (_ : Type) => ())
local notation "core.iter.traits.iterator.Iterator.all.default" => PublicationWriteRuntime.allWindows
local notation "core.option.Option.Insts.CoreCmpPartialEqOption" => PublicationWriteRuntime.optionCmp

/-- [bulksketch::sketch::api::DecodeOutcome]
    Source: 'src/sketch/api.rs', lines 49:0-62:1
    Visibility: public -/
@[discriminant isize]
inductive sketch.api.DecodeOutcome where
| Equal : sketch.api.DecodeOutcome
| Decoded : Slice Std.U64 → sketch.api.DecodeOutcome
| Failed : types.DecodeFailure → sketch.api.DecodeOutcome

/-- [bulksketch::sketch::api::{bulksketch::sketch::api::Publication<'s>}::write::{closure}]
    Source: 'src/sketch/api.rs', lines 289:30-289:66 -/
@[reducible]
def sketch.api.Publication.write.closure := Slice Std.U64

/-- [bulksketch::sketch::api::{bulksketch::sketch::api::Publication<'s>}::write::{closure#1}]
    Source: 'src/sketch/api.rs', lines 282:46-282:61 -/
@[reducible]
def sketch.api.Publication.write.closure_1 := Unit

/-- [bulksketch::sketch::api::{bulksketch::sketch::api::Publication<'s>}::write::{impl core::ops::function::FnOnce<(usize,), core::option::Option<usize>> for bulksketch::sketch::api::{bulksketch::sketch::api::Publication<'s>}::write::{closure}<'s, '_1, '_2>}::call_once]:
    Source: 'src/sketch/api.rs', lines 289:30-289:66 -/
def
  sketch.api.Publication.write.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOptionUsize.call_once
  (c : sketch.api.Publication.write.closure) (tupled_args : Std.Usize) :
  Result (Option Std.Usize)
  := do
  let i := Slice.len c
  ok (Usize.checked_add tupled_args i)

/-- Trait implementation: [bulksketch::sketch::api::{bulksketch::sketch::api::Publication<'s>}::write::{impl core::ops::function::FnOnce<(usize,), core::option::Option<usize>> for bulksketch::sketch::api::{bulksketch::sketch::api::Publication<'s>}::write::{closure}<'s, '_1, '_2>}]
    Source: 'src/sketch/api.rs', lines 289:30-289:66 -/
@[reducible]
def
  sketch.api.Publication.write.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOptionUsize
  : core.ops.function.FnOnce sketch.api.Publication.write.closure Std.Usize
  (Option Std.Usize) := {
  call_once :=
    sketch.api.Publication.write.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOptionUsize.call_once
}

/-- [bulksketch::sketch::api::{bulksketch::sketch::api::Publication<'s>}::write::{impl core::ops::function::FnMut<(&'_2 [u64],), bool> for bulksketch::sketch::api::{bulksketch::sketch::api::Publication<'s>}::write::{closure#1}<'s, '_1, '_2>}::call_mut]:
    Source: 'src/sketch/api.rs', lines 282:46-282:61 -/
def
  sketch.api.Publication.write.closure_1.Insts.CoreOpsFunctionFnMutTupleShared1SliceU64Bool.call_mut
  (c : sketch.api.Publication.write.closure_1) (tupled_args : Slice Std.U64) :
  Result (Bool × sketch.api.Publication.write.closure_1)
  := do
  let i ← Slice.index_usize tupled_args 0#usize
  let i1 ← Slice.index_usize tupled_args 1#usize
  ok (i < i1, ())

/-- [bulksketch::sketch::api::{bulksketch::sketch::api::Publication<'s>}::write::{impl core::ops::function::FnOnce<(&'_2 [u64],), bool> for bulksketch::sketch::api::{bulksketch::sketch::api::Publication<'s>}::write::{closure#1}<'s, '_1, '_2>}::call_once]:
    Source: 'src/sketch/api.rs', lines 282:46-282:61 -/
def
  sketch.api.Publication.write.closure_1.Insts.CoreOpsFunctionFnOnceTupleShared1SliceU64Bool.call_once
  (c : sketch.api.Publication.write.closure_1) (s : Slice Std.U64) :
  Result Bool
  := do
  let (b, _) ←
    sketch.api.Publication.write.closure_1.Insts.CoreOpsFunctionFnMutTupleShared1SliceU64Bool.call_mut
      () s
  ok b

/-- Trait implementation: [bulksketch::sketch::api::{bulksketch::sketch::api::Publication<'s>}::write::{impl core::ops::function::FnOnce<(&'_2 [u64],), bool> for bulksketch::sketch::api::{bulksketch::sketch::api::Publication<'s>}::write::{closure#1}<'s, '_1, '_2>}]
    Source: 'src/sketch/api.rs', lines 282:46-282:61 -/
@[reducible]
def
  sketch.api.Publication.write.closure_1.Insts.CoreOpsFunctionFnOnceTupleShared1SliceU64Bool
  : core.ops.function.FnOnce sketch.api.Publication.write.closure_1 (Slice
  Std.U64) Bool := {
  call_once :=
    sketch.api.Publication.write.closure_1.Insts.CoreOpsFunctionFnOnceTupleShared1SliceU64Bool.call_once
}

/-- Trait implementation: [bulksketch::sketch::api::{bulksketch::sketch::api::Publication<'s>}::write::{impl core::ops::function::FnMut<(&'_2 [u64],), bool> for bulksketch::sketch::api::{bulksketch::sketch::api::Publication<'s>}::write::{closure#1}<'s, '_1, '_2>}]
    Source: 'src/sketch/api.rs', lines 282:46-282:61 -/
@[reducible]
def
  sketch.api.Publication.write.closure_1.Insts.CoreOpsFunctionFnMutTupleShared1SliceU64Bool
  : core.ops.function.FnMut sketch.api.Publication.write.closure_1 (Slice
  Std.U64) Bool := {
  FnOnceInst :=
    sketch.api.Publication.write.closure_1.Insts.CoreOpsFunctionFnOnceTupleShared1SliceU64Bool
  call_mut :=
    sketch.api.Publication.write.closure_1.Insts.CoreOpsFunctionFnMutTupleShared1SliceU64Bool.call_mut
}

/-- [bulksketch::sketch::api::{bulksketch::sketch::api::Publication<'s>}::write]:
    Source: 'src/sketch/api.rs', lines 262:4-312:5 -/
def sketch.api.Publication.write
  (self : sketch.api.Publication) (bucket : Std.Usize)
  (outcome : sketch.api.DecodeOutcome) (zero : Bool) :
  Result (sketch.api.Publication × (sketch.api.Publication →
    sketch.api.Publication))
  := do
  let b := core.option.Option.is_none self.failure
  massert b
  massert (bucket = self.written)
  massert (bucket < self.rows)
  match outcome with
  | sketch.api.DecodeOutcome.Equal =>
    let s ←
      Slice.update self.results.outcomes bucket
        ({
           status := sketch.api.OutcomeStatus.Equal,
           start := 0#u64,
           len := 0#u64
         } : sketch.api.StoredOutcome)
    let i ← self.written + 1#usize
    let back's := fun self1 => { self with results := self1.results }
    ok
      ({ self with results := { self.results with outcomes := s }, written := i
       }, back's)
  | sketch.api.DecodeOutcome.Decoded ids =>
    let b1 ← core.slice.Slice.is_empty ids
    massert ((¬ b1) || zero)
    if b1
    then
      let o ← core.slice.Slice.first ids
      let b2 ←
        core.cmp.PartialEq.ne.trait_default
          (core.option.Option.Insts.CoreCmpPartialEqOption
          (core.cmp.PartialEqShared core.cmp.PartialEqU64)) o (some 0#u64)
      massert b2
      let w ← core.slice.Slice.windows ids 2#usize
      let (b3, _) ←
        core.iter.traits.iterator.Iterator.all.default
          (core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice
          Std.U64)
          sketch.api.Publication.write.closure_1.Insts.CoreOpsFunctionFnMutTupleShared1SliceU64Bool
          w ()
      massert b3
      let «prefix» ← lift (core.convert.num.FromUsizeBool.from zero)
      let o1 ← lift (Usize.checked_add self.used_ids «prefix»)
      let o2 ←
        core.option.Option.and_then
          sketch.api.Publication.write.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOptionUsize
          o1 ids
      let «end» ←
        core.option.Option.expect o2 (toStr "admitted result offsets")
      massert («end» <= self.id_capacity)
      if zero
      then
        let s ← Slice.update self.results.ids self.used_ids 0#u64
        let i ← self.used_ids + «prefix»
        let (destination, index_mut_back) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) s
            { start := i, «end» }
        let i1 := Slice.len ids
        if i1 = 1#usize
        then
          let id ← Slice.index_usize ids 0#usize
          let destination1 ← Slice.update destination 0#usize id
          let r ←
            U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
              self.used_ids
          let start ←
            core.result.Result.expect
              core.num.error.TryFromIntError.Insts.CoreFmtDebug r (toStr
              "result offset fits u64")
          let i2 ← «end» - self.used_ids
          let r1 ←
            U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from i2
          let len ←
            core.result.Result.expect
              core.num.error.TryFromIntError.Insts.CoreFmtDebug r1 (toStr
              "result length fits u64")
          let s1 ←
            Slice.update self.results.outcomes bucket
              ({ status := sketch.api.OutcomeStatus.Decoded, start, len } :
              sketch.api.StoredOutcome)
          let i3 ← self.written + 1#usize
          let s2 := index_mut_back destination1
          let back's := fun self1 => { self with results := self1.results }
          ok
            ({
               self
                 with
                 results := { ids := s2, outcomes := s1 },
                 written := i3,
                 used_ids := «end»
             }, back's)
        else
          let i2 := Slice.len ids
          if i2 = 2#usize
          then
            let first ← Slice.index_usize ids 0#usize
            let second ← Slice.index_usize ids 1#usize
            let destination1 ← Slice.update destination 0#usize first
            let destination2 ← Slice.update destination1 1#usize second
            let r ←
              U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
                self.used_ids
            let start ←
              core.result.Result.expect
                core.num.error.TryFromIntError.Insts.CoreFmtDebug r (toStr
                "result offset fits u64")
            let i3 ← «end» - self.used_ids
            let r1 ←
              U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from i3
            let len ←
              core.result.Result.expect
                core.num.error.TryFromIntError.Insts.CoreFmtDebug r1 (toStr
                "result length fits u64")
            let s1 ←
              Slice.update self.results.outcomes bucket
                ({ status := sketch.api.OutcomeStatus.Decoded, start, len } :
                sketch.api.StoredOutcome)
            let i4 ← self.written + 1#usize
            let s2 := index_mut_back destination2
            let back's := fun self1 => { self with results := self1.results }
            ok
              ({
                 self
                   with
                   results := { ids := s2, outcomes := s1 },
                   written := i4,
                   used_ids := «end»
               }, back's)
          else
            let destination1 ←
              core.slice.Slice.copy_from_slice core.marker.CopyU64 destination
                ids
            let r ←
              U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
                self.used_ids
            let start ←
              core.result.Result.expect
                core.num.error.TryFromIntError.Insts.CoreFmtDebug r (toStr
                "result offset fits u64")
            let i3 ← «end» - self.used_ids
            let r1 ←
              U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from i3
            let len ←
              core.result.Result.expect
                core.num.error.TryFromIntError.Insts.CoreFmtDebug r1 (toStr
                "result length fits u64")
            let s1 ←
              Slice.update self.results.outcomes bucket
                ({ status := sketch.api.OutcomeStatus.Decoded, start, len } :
                sketch.api.StoredOutcome)
            let i4 ← self.written + 1#usize
            let s2 := index_mut_back destination1
            let back's := fun self1 => { self with results := self1.results }
            ok
              ({
                 self
                   with
                   results := { ids := s2, outcomes := s1 },
                   written := i4,
                   used_ids := «end»
               }, back's)
      else
        let i ← self.used_ids + «prefix»
        let (destination, index_mut_back) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U64)
            self.results.ids { start := i, «end» }
        let i1 := Slice.len ids
        if i1 = 1#usize
        then
          let id ← Slice.index_usize ids 0#usize
          let destination1 ← Slice.update destination 0#usize id
          let r ←
            U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
              self.used_ids
          let start ←
            core.result.Result.expect
              core.num.error.TryFromIntError.Insts.CoreFmtDebug r (toStr
              "result offset fits u64")
          let i2 ← «end» - self.used_ids
          let r1 ←
            U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from i2
          let len ←
            core.result.Result.expect
              core.num.error.TryFromIntError.Insts.CoreFmtDebug r1 (toStr
              "result length fits u64")
          let s ←
            Slice.update self.results.outcomes bucket
              ({ status := sketch.api.OutcomeStatus.Decoded, start, len } :
              sketch.api.StoredOutcome)
          let i3 ← self.written + 1#usize
          let s1 := index_mut_back destination1
          let back's := fun self1 => { self with results := self1.results }
          ok
            ({
               self
                 with
                 results := { ids := s1, outcomes := s },
                 written := i3,
                 used_ids := «end»
             }, back's)
        else
          let i2 := Slice.len ids
          if i2 = 2#usize
          then
            let first ← Slice.index_usize ids 0#usize
            let second ← Slice.index_usize ids 1#usize
            let destination1 ← Slice.update destination 0#usize first
            let destination2 ← Slice.update destination1 1#usize second
            let r ←
              U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
                self.used_ids
            let start ←
              core.result.Result.expect
                core.num.error.TryFromIntError.Insts.CoreFmtDebug r (toStr
                "result offset fits u64")
            let i3 ← «end» - self.used_ids
            let r1 ←
              U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from i3
            let len ←
              core.result.Result.expect
                core.num.error.TryFromIntError.Insts.CoreFmtDebug r1 (toStr
                "result length fits u64")
            let s ←
              Slice.update self.results.outcomes bucket
                ({ status := sketch.api.OutcomeStatus.Decoded, start, len } :
                sketch.api.StoredOutcome)
            let i4 ← self.written + 1#usize
            let s1 := index_mut_back destination2
            let back's := fun self1 => { self with results := self1.results }
            ok
              ({
                 self
                   with
                   results := { ids := s1, outcomes := s },
                   written := i4,
                   used_ids := «end»
               }, back's)
          else
            let destination1 ←
              core.slice.Slice.copy_from_slice core.marker.CopyU64 destination
                ids
            let r ←
              U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
                self.used_ids
            let start ←
              core.result.Result.expect
                core.num.error.TryFromIntError.Insts.CoreFmtDebug r (toStr
                "result offset fits u64")
            let i3 ← «end» - self.used_ids
            let r1 ←
              U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from i3
            let len ←
              core.result.Result.expect
                core.num.error.TryFromIntError.Insts.CoreFmtDebug r1 (toStr
                "result length fits u64")
            let s ←
              Slice.update self.results.outcomes bucket
                ({ status := sketch.api.OutcomeStatus.Decoded, start, len } :
                sketch.api.StoredOutcome)
            let i4 ← self.written + 1#usize
            let s1 := index_mut_back destination1
            let back's := fun self1 => { self with results := self1.results }
            ok
              ({
                 self
                   with
                   results := { ids := s1, outcomes := s },
                   written := i4,
                   used_ids := «end»
               }, back's)
    else
      let o ← core.slice.Slice.first ids
      let b2 ←
        core.cmp.PartialEq.ne.trait_default
          (core.option.Option.Insts.CoreCmpPartialEqOption
          (core.cmp.PartialEqShared core.cmp.PartialEqU64)) o (some 0#u64)
      massert b2
      let w ← core.slice.Slice.windows ids 2#usize
      let (b3, _) ←
        core.iter.traits.iterator.Iterator.all.default
          (core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice
          Std.U64)
          sketch.api.Publication.write.closure_1.Insts.CoreOpsFunctionFnMutTupleShared1SliceU64Bool
          w ()
      massert b3
      let «prefix» ← lift (core.convert.num.FromUsizeBool.from zero)
      let o1 ← lift (Usize.checked_add self.used_ids «prefix»)
      let o2 ←
        core.option.Option.and_then
          sketch.api.Publication.write.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOptionUsize
          o1 ids
      let «end» ←
        core.option.Option.expect o2 (toStr "admitted result offsets")
      massert («end» <= self.id_capacity)
      if zero
      then
        let s ← Slice.update self.results.ids self.used_ids 0#u64
        let i ← self.used_ids + «prefix»
        let (destination, index_mut_back) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) s
            { start := i, «end» }
        let i1 := Slice.len ids
        if i1 = 1#usize
        then
          let id ← Slice.index_usize ids 0#usize
          let destination1 ← Slice.update destination 0#usize id
          let r ←
            U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
              self.used_ids
          let start ←
            core.result.Result.expect
              core.num.error.TryFromIntError.Insts.CoreFmtDebug r (toStr
              "result offset fits u64")
          let i2 ← «end» - self.used_ids
          let r1 ←
            U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from i2
          let len ←
            core.result.Result.expect
              core.num.error.TryFromIntError.Insts.CoreFmtDebug r1 (toStr
              "result length fits u64")
          let s1 ←
            Slice.update self.results.outcomes bucket
              ({ status := sketch.api.OutcomeStatus.Decoded, start, len } :
              sketch.api.StoredOutcome)
          let i3 ← self.written + 1#usize
          let s2 := index_mut_back destination1
          let back's := fun self1 => { self with results := self1.results }
          ok
            ({
               self
                 with
                 results := { ids := s2, outcomes := s1 },
                 written := i3,
                 used_ids := «end»
             }, back's)
        else
          let i2 := Slice.len ids
          if i2 = 2#usize
          then
            let first ← Slice.index_usize ids 0#usize
            let second ← Slice.index_usize ids 1#usize
            let destination1 ← Slice.update destination 0#usize first
            let destination2 ← Slice.update destination1 1#usize second
            let r ←
              U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
                self.used_ids
            let start ←
              core.result.Result.expect
                core.num.error.TryFromIntError.Insts.CoreFmtDebug r (toStr
                "result offset fits u64")
            let i3 ← «end» - self.used_ids
            let r1 ←
              U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from i3
            let len ←
              core.result.Result.expect
                core.num.error.TryFromIntError.Insts.CoreFmtDebug r1 (toStr
                "result length fits u64")
            let s1 ←
              Slice.update self.results.outcomes bucket
                ({ status := sketch.api.OutcomeStatus.Decoded, start, len } :
                sketch.api.StoredOutcome)
            let i4 ← self.written + 1#usize
            let s2 := index_mut_back destination2
            let back's := fun self1 => { self with results := self1.results }
            ok
              ({
                 self
                   with
                   results := { ids := s2, outcomes := s1 },
                   written := i4,
                   used_ids := «end»
               }, back's)
          else
            let destination1 ←
              core.slice.Slice.copy_from_slice core.marker.CopyU64 destination
                ids
            let r ←
              U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
                self.used_ids
            let start ←
              core.result.Result.expect
                core.num.error.TryFromIntError.Insts.CoreFmtDebug r (toStr
                "result offset fits u64")
            let i3 ← «end» - self.used_ids
            let r1 ←
              U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from i3
            let len ←
              core.result.Result.expect
                core.num.error.TryFromIntError.Insts.CoreFmtDebug r1 (toStr
                "result length fits u64")
            let s1 ←
              Slice.update self.results.outcomes bucket
                ({ status := sketch.api.OutcomeStatus.Decoded, start, len } :
                sketch.api.StoredOutcome)
            let i4 ← self.written + 1#usize
            let s2 := index_mut_back destination1
            let back's := fun self1 => { self with results := self1.results }
            ok
              ({
                 self
                   with
                   results := { ids := s2, outcomes := s1 },
                   written := i4,
                   used_ids := «end»
               }, back's)
      else
        let i ← self.used_ids + «prefix»
        let (destination, index_mut_back) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U64)
            self.results.ids { start := i, «end» }
        let i1 := Slice.len ids
        if i1 = 1#usize
        then
          let id ← Slice.index_usize ids 0#usize
          let destination1 ← Slice.update destination 0#usize id
          let r ←
            U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
              self.used_ids
          let start ←
            core.result.Result.expect
              core.num.error.TryFromIntError.Insts.CoreFmtDebug r (toStr
              "result offset fits u64")
          let i2 ← «end» - self.used_ids
          let r1 ←
            U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from i2
          let len ←
            core.result.Result.expect
              core.num.error.TryFromIntError.Insts.CoreFmtDebug r1 (toStr
              "result length fits u64")
          let s ←
            Slice.update self.results.outcomes bucket
              ({ status := sketch.api.OutcomeStatus.Decoded, start, len } :
              sketch.api.StoredOutcome)
          let i3 ← self.written + 1#usize
          let s1 := index_mut_back destination1
          let back's := fun self1 => { self with results := self1.results }
          ok
            ({
               self
                 with
                 results := { ids := s1, outcomes := s },
                 written := i3,
                 used_ids := «end»
             }, back's)
        else
          let i2 := Slice.len ids
          if i2 = 2#usize
          then
            let first ← Slice.index_usize ids 0#usize
            let second ← Slice.index_usize ids 1#usize
            let destination1 ← Slice.update destination 0#usize first
            let destination2 ← Slice.update destination1 1#usize second
            let r ←
              U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
                self.used_ids
            let start ←
              core.result.Result.expect
                core.num.error.TryFromIntError.Insts.CoreFmtDebug r (toStr
                "result offset fits u64")
            let i3 ← «end» - self.used_ids
            let r1 ←
              U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from i3
            let len ←
              core.result.Result.expect
                core.num.error.TryFromIntError.Insts.CoreFmtDebug r1 (toStr
                "result length fits u64")
            let s ←
              Slice.update self.results.outcomes bucket
                ({ status := sketch.api.OutcomeStatus.Decoded, start, len } :
                sketch.api.StoredOutcome)
            let i4 ← self.written + 1#usize
            let s1 := index_mut_back destination2
            let back's := fun self1 => { self with results := self1.results }
            ok
              ({
                 self
                   with
                   results := { ids := s1, outcomes := s },
                   written := i4,
                   used_ids := «end»
               }, back's)
          else
            let destination1 ←
              core.slice.Slice.copy_from_slice core.marker.CopyU64 destination
                ids
            let r ←
              U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
                self.used_ids
            let start ←
              core.result.Result.expect
                core.num.error.TryFromIntError.Insts.CoreFmtDebug r (toStr
                "result offset fits u64")
            let i3 ← «end» - self.used_ids
            let r1 ←
              U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from i3
            let len ←
              core.result.Result.expect
                core.num.error.TryFromIntError.Insts.CoreFmtDebug r1 (toStr
                "result length fits u64")
            let s ←
              Slice.update self.results.outcomes bucket
                ({ status := sketch.api.OutcomeStatus.Decoded, start, len } :
                sketch.api.StoredOutcome)
            let i4 ← self.written + 1#usize
            let s1 := index_mut_back destination1
            let back's := fun self1 => { self with results := self1.results }
            ok
              ({
                 self
                   with
                   results := { ids := s1, outcomes := s },
                   written := i4,
                   used_ids := «end»
               }, back's)
  | sketch.api.DecodeOutcome.Failed reason =>
    let status ←
      match reason with
      | types.DecodeFailure.DegreeExceedsBudget =>
        ok sketch.api.OutcomeStatus.DegreeExceedsBudget
      | types.DecodeFailure.InvalidLocator =>
        ok sketch.api.OutcomeStatus.InvalidLocator
      | types.DecodeFailure.NotSplit => ok sketch.api.OutcomeStatus.NotSplit
      | types.DecodeFailure.VerificationFailed =>
        ok sketch.api.OutcomeStatus.VerificationFailed
    let s ←
      Slice.update self.results.outcomes bucket
        ({ status, start := 0#u64, len := 0#u64 } : sketch.api.StoredOutcome)
    let i ← self.written + 1#usize
    let back's := fun self1 => { self with results := self1.results }
    ok
      ({ self with results := { self.results with outcomes := s }, written := i
       }, back's)

end bulksketch
