-- Exact original DegreeProbe declarations with scoped standard-library bindings.
import Arithmetic.ReconstructionTypes
import Arithmetic.WorkScheduleGenerated
import Arithmetic.QuarticGenerated
import Arithmetic.RebuiltLfsrGenerated
import Arithmetic.Funs
import Arithmetic.NewtonGuardGenerated
import Arithmetic.NormalizeGenerated
import Arithmetic.DegreeProbeRuntime

namespace bulksketch

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
set_option maxRecDepth 2048
set_option maxHeartbeats 1500000

local notation "core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice" =>
  RebuiltLfsrRuntime.inclusive
local notation "Mut1A.Insts.CoreCmpPartialEqShared0B.eq" => CertificateRuntime.mutableSharedEq
local notation "core.bool.Bool.then_some" => CubeRootRuntime.thenSome
local notation "U8.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from" =>
  Aeneas.Std.DegreeProbeRuntime.usizeToU8
local notation "core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold" =>
  Aeneas.Std.DegreeProbeRuntime.foldShared
local notation "core.slice.Slice.sort_unstable" =>
  (fun (_ : core.cmp.Ord U64) => Aeneas.Std.DegreeProbeRuntime.sortUnsigned)

/-- [bulksketch::decode::probe::verified::{closure#1}]
    Source: 'src/decode/probe.rs', lines 176:40-176:75 -/
@[reducible]
def decode.probe.verified.closure_1 (F : Type _) (K : Type _) := Unit

/-- [bulksketch::decode::probe::verified::{closure}]
    Source: 'src/decode/probe.rs', lines 174:33-174:46 -/
@[reducible]
def decode.probe.verified.closure (F : Type _) (K : Type _) := Unit

/-- [bulksketch::decode::degree_probe::{bulksketch::decode::degree_probe::DegreeProbe}::new]:
    Source: 'src/decode/degree_probe.rs', lines 27:4-33:5 -/
def decode.degree_probe.DegreeProbe.new
  (budget : decode.row.RowBudget) (capacity : Std.Usize) :
  Result (Option decode.degree_probe.DegreeProbe)
  := do
  let b ←
    if budget.nonzero >= 3#usize
    then ok (capacity >= 3#usize)
    else ok false
  core.bool.Bool.then_some b
    ({ degree := 3#u8, count := 0#u8, next := (some types.Stage.GuardThree) } :
    decode.degree_probe.DegreeProbe)

/-- [bulksketch::decode::degree_probe::{bulksketch::decode::degree_probe::DegreeProbe}::next_stage]:
    Source: 'src/decode/degree_probe.rs', lines 34:4-36:5 -/
def decode.degree_probe.DegreeProbe.next_stage
  (self : decode.degree_probe.DegreeProbe) : Result (Option types.Stage) := do
  ok self.next

/-- [bulksketch::decode::degree_probe::{bulksketch::decode::degree_probe::DegreeProbe}::count]:
    Source: 'src/decode/degree_probe.rs', lines 37:4-39:5 -/
def decode.degree_probe.DegreeProbe.impl.count
  (self : decode.degree_probe.DegreeProbe) : Result Std.Usize := do
  ok (core.convert.num.FromUsizeU8.from self.count)

/-- [bulksketch::decode::degree_probe::{bulksketch::decode::degree_probe::DegreeProbe}::reject]:
    Source: 'src/decode/degree_probe.rs', lines 40:4-50:5 -/
def decode.degree_probe.DegreeProbe.reject
  (self : decode.degree_probe.DegreeProbe) (capacity : Std.Usize)
  (budget : decode.row.RowBudget) :
  Result decode.degree_probe.DegreeProbe
  := do
  if self.degree = 3#u8
  then
    if capacity >= 4#usize
    then
      if budget.nonzero >= 4#usize
      then
        ok
          { degree := 4#u8, count := 0#u8, next := (some types.Stage.GuardFour)
          }
      else
        ok
          { self with count := 0#u8, next := (some types.Stage.Reconstruction)
          }
    else
      ok { self with count := 0#u8, next := (some types.Stage.Reconstruction) }
  else
    ok { self with count := 0#u8, next := (some types.Stage.Reconstruction) }

/-- [bulksketch::decode::probe::verified::{impl core::ops::function::FnMut<(u64, &'_0 u64), u64> for bulksketch::decode::probe::verified::{closure#1}<'_0, F, K>}::call_mut]:
    Source: 'src/decode/probe.rs', lines 176:40-176:75 -/
def
  decode.probe.verified.closure_1.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64.call_mut
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.probe.verified.closure_1 F K)
  (tupled_args : (Std.U64 × Std.U64)) :
  Result (Std.U64 × (decode.probe.verified.closure_1 F K))
  := do
  let (s, x) := tupled_args
  let i ← backendcontractBulkKernelsInst.ArithmeticInst.square x
  let i1 ← backendcontractBulkKernelsInst.ArithmeticInst.mul x i
  let i2 ← lift (s ^^^ i1)
  ok (i2, ())

/-- [bulksketch::decode::probe::verified::{impl core::ops::function::FnOnce<(u64, &'_0 u64), u64> for bulksketch::decode::probe::verified::{closure#1}<'_0, F, K>}::call_once]:
    Source: 'src/decode/probe.rs', lines 176:40-176:75 -/
def
  decode.probe.verified.closure_1.Insts.CoreOpsFunctionFnOncePairU64Shared0U64U64.call_once
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.probe.verified.closure_1 F K) (p : (Std.U64 × Std.U64)) :
  Result Std.U64
  := do
  let (i, _) ←
    decode.probe.verified.closure_1.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64.call_mut
      fieldBinaryFieldInst backendcontractBulkKernelsInst () p
  ok i

/-- Trait implementation: [bulksketch::decode::probe::verified::{impl core::ops::function::FnOnce<(u64, &'_0 u64), u64> for bulksketch::decode::probe::verified::{closure#1}<'_0, F, K>}]
    Source: 'src/decode/probe.rs', lines 176:40-176:75 -/
@[reducible]
def
  decode.probe.verified.closure_1.Insts.CoreOpsFunctionFnOncePairU64Shared0U64U64
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnOnce (decode.probe.verified.closure_1 F K) (Std.U64 ×
  Std.U64) Std.U64 := {
  call_once :=
    decode.probe.verified.closure_1.Insts.CoreOpsFunctionFnOncePairU64Shared0U64U64.call_once
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- Trait implementation: [bulksketch::decode::probe::verified::{impl core::ops::function::FnMut<(u64, &'_0 u64), u64> for bulksketch::decode::probe::verified::{closure#1}<'_0, F, K>}]
    Source: 'src/decode/probe.rs', lines 176:40-176:75 -/
@[reducible]
def
  decode.probe.verified.closure_1.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnMut (decode.probe.verified.closure_1 F K) (Std.U64 ×
  Std.U64) Std.U64 := {
  FnOnceInst :=
    decode.probe.verified.closure_1.Insts.CoreOpsFunctionFnOncePairU64Shared0U64U64
    fieldBinaryFieldInst backendcontractBulkKernelsInst
  call_mut :=
    decode.probe.verified.closure_1.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64.call_mut
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- [bulksketch::decode::probe::verified::{impl core::ops::function::FnMut<(u64, &'_0 u64), u64> for bulksketch::decode::probe::verified::{closure}<'_0, F, K>}::call_mut]:
    Source: 'src/decode/probe.rs', lines 174:33-174:46 -/
def
  decode.probe.verified.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64.call_mut
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.probe.verified.closure F K) (tupled_args : (Std.U64 × Std.U64))
  :
  Result (Std.U64 × (decode.probe.verified.closure F K))
  := do
  let (s, x) := tupled_args
  let i ← lift (s ^^^ x)
  ok (i, ())

/-- [bulksketch::decode::probe::verified::{impl core::ops::function::FnOnce<(u64, &'_0 u64), u64> for bulksketch::decode::probe::verified::{closure}<'_0, F, K>}::call_once]:
    Source: 'src/decode/probe.rs', lines 174:33-174:46 -/
def
  decode.probe.verified.closure.Insts.CoreOpsFunctionFnOncePairU64Shared0U64U64.call_once
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.probe.verified.closure F K) (p : (Std.U64 × Std.U64)) :
  Result Std.U64
  := do
  let (i, _) ←
    decode.probe.verified.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64.call_mut
      fieldBinaryFieldInst backendcontractBulkKernelsInst () p
  ok i

/-- Trait implementation: [bulksketch::decode::probe::verified::{impl core::ops::function::FnOnce<(u64, &'_0 u64), u64> for bulksketch::decode::probe::verified::{closure}<'_0, F, K>}]
    Source: 'src/decode/probe.rs', lines 174:33-174:46 -/
@[reducible]
def
  decode.probe.verified.closure.Insts.CoreOpsFunctionFnOncePairU64Shared0U64U64
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnOnce (decode.probe.verified.closure F K) (Std.U64 ×
  Std.U64) Std.U64 := {
  call_once :=
    decode.probe.verified.closure.Insts.CoreOpsFunctionFnOncePairU64Shared0U64U64.call_once
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- Trait implementation: [bulksketch::decode::probe::verified::{impl core::ops::function::FnMut<(u64, &'_0 u64), u64> for bulksketch::decode::probe::verified::{closure}<'_0, F, K>}]
    Source: 'src/decode/probe.rs', lines 174:33-174:46 -/
@[reducible]
def
  decode.probe.verified.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnMut (decode.probe.verified.closure F K) (Std.U64 ×
  Std.U64) Std.U64 := {
  FnOnceInst :=
    decode.probe.verified.closure.Insts.CoreOpsFunctionFnOncePairU64Shared0U64U64
    fieldBinaryFieldInst backendcontractBulkKernelsInst
  call_mut :=
    decode.probe.verified.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64.call_mut
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- [bulksketch::decode::probe::verified]:
    Source: 'src/decode/probe.rs', lines 168:0-183:1 -/
def decode.probe.verified
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (difference : Slice Std.U64) (roots : Slice Std.U64)
  (verification : Slice Std.U64) :
  Result (Bool × (Slice Std.U64))
  := do
  let i := Slice.len roots
  if i <= 2#usize
  then
    let i1 ← core.slice.Slice.iter roots
    let i2 ←
      core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold
        (decode.probe.verified.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64
        fieldBinaryFieldInst backendcontractBulkKernelsInst) i1 0#u64 ()
    let i3 ← Slice.index_usize difference 0#usize
    if i2 != i3
    then ok (false, verification)
    else
      let i4 := Slice.len difference
      if i4 >= 2#usize
      then
        let i5 ←
          core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold
            (decode.probe.verified.closure_1.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64
            fieldBinaryFieldInst backendcontractBulkKernelsInst) i1 0#u64 ()
        let i6 ← Slice.index_usize difference 1#usize
        if i5 != i6
        then ok (false, verification)
        else
          let i7 := Slice.len difference
          let (verification1, index_mut_back) ←
            core.slice.index.Slice.index_mut
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
              verification { «end» := i7 }
          let verification2 ←
            backendcontractBulkKernelsInst.encode_nonzero verification1 roots
          let b ←
            Mut1A.Insts.CoreCmpPartialEqShared0B.eq
              (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU64)
              verification2 difference
          let verification3 := index_mut_back verification2
          ok (b, verification3)
      else
        let i5 := Slice.len difference
        let (verification1, index_mut_back) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) verification
            { «end» := i5 }
        let verification2 ←
          backendcontractBulkKernelsInst.encode_nonzero verification1 roots
        let b ←
          Mut1A.Insts.CoreCmpPartialEqShared0B.eq
            (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU64)
            verification2 difference
        let verification3 := index_mut_back verification2
        ok (b, verification3)
  else
    let i1 := Slice.len difference
    let (verification1, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) verification
        { «end» := i1 }
    let verification2 ←
      backendcontractBulkKernelsInst.encode_nonzero verification1 roots
    let b ←
      Mut1A.Insts.CoreCmpPartialEqShared0B.eq
        (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU64) verification2
        difference
    let verification3 := index_mut_back verification2
    ok (b, verification3)

/-- [bulksketch::decode::degree_probe::{bulksketch::decode::degree_probe::DegreeProbe}::run]:
    Source: 'src/decode/degree_probe.rs', lines 51:4-139:5 -/
def decode.degree_probe.DegreeProbe.run
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (self : decode.degree_probe.DegreeProbe) (odd : Slice Std.U64)
  (budget : decode.row.RowBudget) (workspace : decode.scratch.RowWorkspace)
  (meter : types.WorkMeter) :
  Result ((core.result.Result (Option types.Stage) types.DecodeError) ×
    decode.degree_probe.DegreeProbe × decode.scratch.RowWorkspace ×
    (decode.scratch.RowWorkspace → decode.scratch.RowWorkspace) ×
    types.WorkMeter)
  := do
  let stage ←
    core.option.Option.expect self.next (toStr "active degree probe")
  let degree ← lift (core.convert.num.FromUsizeU8.from self.degree)
  let count ← decode.degree_probe.DegreeProbe.impl.count self
  let (budget1, operation) ←
    match stage with
    | types.Stage.DirectOne => fail panic
    | types.Stage.DirectTwo => fail panic
    | types.Stage.GuardThree => ok (budget, decode.work.Charge.GuardThree)
    | types.Stage.NewtonThree => ok (budget, decode.work.Charge.NewtonThree)
    | types.Stage.GuardFour => ok (budget, decode.work.Charge.GuardFour)
    | types.Stage.NewtonFour => ok (budget, decode.work.Charge.NewtonFour)
    | types.Stage.LeafThree => ok (budget, decode.work.Charge.LeafThree)
    | types.Stage.LeafFour => ok (budget, decode.work.Charge.LeafFour)
    | types.Stage.FactorVerification =>
      ok (budget, decode.work.Charge.FactorVerification degree)
    | types.Stage.Reconstruction => fail panic
    | types.Stage.BerlekampMassey => fail panic
    | types.Stage.CandidateEvaluation => fail panic
    | types.Stage.Deflation => fail panic
    | types.Stage.ReducerPreparation => fail panic
    | types.Stage.AffinePreparation => fail panic
    | types.Stage.AffineEnumeration => fail panic
    | types.Stage.AffineSplit => fail panic
    | types.Stage.Trace => fail panic
    | types.Stage.Gcd => fail panic
    | types.Stage.FactorDivision => fail panic
    | types.Stage.Leaf => fail panic
    | types.Stage.Verification =>
      let i := Slice.len odd
      ok (budget, decode.work.Charge.Verify i budget.total)
    | types.Stage.Canonicalization =>
      ok (budget, decode.work.Charge.Canonicalize budget.total)
  let r ← decode.work.WorkScheduleV1.cost operation
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (r1, meter1) ← types.WorkMeter.charge meter val
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      match stage with
      | types.Stage.DirectOne => fail panic
      | types.Stage.DirectTwo => fail panic
      | types.Stage.GuardThree =>
        let (s, index_mut_back) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U64)
            workspace.polynomials { start := 5#usize, «end» := 11#usize }
        let (b, s1) ←
          decode.deg34.guard fieldBinaryFieldInst
            backendcontractBulkKernelsInst odd degree s
        if b
        then
          if degree = 3#usize
          then
            let s2 := index_mut_back s1
            ok (core.result.Result.Ok (some types.Stage.NewtonThree),
              { self with next := (some types.Stage.NewtonThree) },
              { workspace with polynomials := s2 },
              fun workspace1 => workspace1, meter1)
          else
            let s2 := index_mut_back s1
            ok (core.result.Result.Ok (some types.Stage.NewtonFour),
              { self with next := (some types.Stage.NewtonFour) },
              { workspace with polynomials := s2 },
              fun workspace1 => workspace1, meter1)
        else
          let i := Slice.len odd
          let self1 ← decode.degree_probe.DegreeProbe.reject self i budget1
          let s2 := index_mut_back s1
          ok (core.result.Result.Ok self1.next, self1,
            { workspace with polynomials := s2 }, fun workspace1 => workspace1,
            meter1)
      | types.Stage.NewtonThree =>
        let ((factor, rest), split_at_mut_back) ←
          core.slice.Slice.split_at_mut workspace.polynomials 5#usize
        let s ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) rest
            { «end» := 6#usize }
        let i ← Slice.index_usize odd 0#usize
        let factor1 ←
          decode.deg34.normalize fieldBinaryFieldInst
            backendcontractBulkKernelsInst s i degree factor
        if degree = 3#usize
        then
          let s1 := split_at_mut_back (factor1, rest)
          ok (core.result.Result.Ok (some types.Stage.LeafThree),
            { self with next := (some types.Stage.LeafThree) },
            { workspace with polynomials := s1 }, fun workspace1 => workspace1,
            meter1)
        else
          let s1 := split_at_mut_back (factor1, rest)
          ok (core.result.Result.Ok (some types.Stage.LeafFour),
            { self with next := (some types.Stage.LeafFour) },
            { workspace with polynomials := s1 }, fun workspace1 => workspace1,
            meter1)
      | types.Stage.GuardFour =>
        let (s, index_mut_back) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U64)
            workspace.polynomials { start := 5#usize, «end» := 11#usize }
        let (b, s1) ←
          decode.deg34.guard fieldBinaryFieldInst
            backendcontractBulkKernelsInst odd degree s
        if b
        then
          if degree = 3#usize
          then
            let s2 := index_mut_back s1
            ok (core.result.Result.Ok (some types.Stage.NewtonThree),
              { self with next := (some types.Stage.NewtonThree) },
              { workspace with polynomials := s2 },
              fun workspace1 => workspace1, meter1)
          else
            let s2 := index_mut_back s1
            ok (core.result.Result.Ok (some types.Stage.NewtonFour),
              { self with next := (some types.Stage.NewtonFour) },
              { workspace with polynomials := s2 },
              fun workspace1 => workspace1, meter1)
        else
          let i := Slice.len odd
          let self1 ← decode.degree_probe.DegreeProbe.reject self i budget1
          let s2 := index_mut_back s1
          ok (core.result.Result.Ok self1.next, self1,
            { workspace with polynomials := s2 }, fun workspace1 => workspace1,
            meter1)
      | types.Stage.NewtonFour =>
        let ((factor, rest), split_at_mut_back) ←
          core.slice.Slice.split_at_mut workspace.polynomials 5#usize
        let s ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) rest
            { «end» := 6#usize }
        let i ← Slice.index_usize odd 0#usize
        let factor1 ←
          decode.deg34.normalize fieldBinaryFieldInst
            backendcontractBulkKernelsInst s i degree factor
        if degree = 3#usize
        then
          let s1 := split_at_mut_back (factor1, rest)
          ok (core.result.Result.Ok (some types.Stage.LeafThree),
            { self with next := (some types.Stage.LeafThree) },
            { workspace with polynomials := s1 }, fun workspace1 => workspace1,
            meter1)
        else
          let s1 := split_at_mut_back (factor1, rest)
          ok (core.result.Result.Ok (some types.Stage.LeafFour),
            { self with next := (some types.Stage.LeafFour) },
            { workspace with polynomials := s1 }, fun workspace1 => workspace1,
            meter1)
      | types.Stage.LeafThree =>
        let ((factor, rest), split_at_mut_back) ←
          core.slice.Slice.split_at_mut workspace.polynomials 11#usize
        let s ←
          core.slice.index.Slice.index
            (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
            Std.U64) factor { «end» := degree }
        let (s1, index_mut_back) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) rest
            { «end» := 4#usize }
        let (o, s2) ←
          decode.deg34.solve fieldBinaryFieldInst
            backendcontractBulkKernelsInst s s1
        match o with
        | none =>
          let i := Slice.len odd
          let self1 ← decode.degree_probe.DegreeProbe.reject self i budget1
          let rest1 := index_mut_back s2
          let s3 := split_at_mut_back (factor, rest1)
          ok (core.result.Result.Ok self1.next, self1,
            { workspace with polynomials := s3 }, fun workspace1 => workspace1,
            meter1)
        | some count1 =>
          let r2 ←
            U8.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from count1
          let i ←
            core.result.Result.expect
              core.num.error.TryFromIntError.Insts.CoreFmtDebug r2 (toStr
              "degree-three/four root count")
          let rest1 := index_mut_back s2
          let s3 := split_at_mut_back (factor, rest1)
          ok (core.result.Result.Ok (some types.Stage.FactorVerification),
            {
              self
                with
                count := i, next := (some types.Stage.FactorVerification)
            }, { workspace with polynomials := s3 },
            fun workspace1 => workspace1, meter1)
      | types.Stage.LeafFour =>
        let ((factor, rest), split_at_mut_back) ←
          core.slice.Slice.split_at_mut workspace.polynomials 11#usize
        let s ←
          core.slice.index.Slice.index
            (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
            Std.U64) factor { «end» := degree }
        let (s1, index_mut_back) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) rest
            { «end» := 4#usize }
        let (o, s2) ←
          decode.deg34.solve fieldBinaryFieldInst
            backendcontractBulkKernelsInst s s1
        match o with
        | none =>
          let i := Slice.len odd
          let self1 ← decode.degree_probe.DegreeProbe.reject self i budget1
          let rest1 := index_mut_back s2
          let s3 := split_at_mut_back (factor, rest1)
          ok (core.result.Result.Ok self1.next, self1,
            { workspace with polynomials := s3 }, fun workspace1 => workspace1,
            meter1)
        | some count1 =>
          let r2 ←
            U8.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from count1
          let i ←
            core.result.Result.expect
              core.num.error.TryFromIntError.Insts.CoreFmtDebug r2 (toStr
              "degree-three/four root count")
          let rest1 := index_mut_back s2
          let s3 := split_at_mut_back (factor, rest1)
          ok (core.result.Result.Ok (some types.Stage.FactorVerification),
            {
              self
                with
                count := i, next := (some types.Stage.FactorVerification)
            }, { workspace with polynomials := s3 },
            fun workspace1 => workspace1, meter1)
      | types.Stage.FactorVerification =>
        let ((values, product), split_at_mut_back) ←
          core.slice.Slice.split_at_mut workspace.polynomials 15#usize
        let s ←
          core.slice.index.Slice.index
            (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
            Std.U64) values { «end» := degree }
        let i ← 11#usize + count
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) values
            { start := 11#usize, «end» := i }
        let (s2, index_mut_back) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) product
            { «end» := 5#usize }
        let (valid, s3) ←
          decode.deg34.certificate fieldBinaryFieldInst
            backendcontractBulkKernelsInst s s1 s2
        if valid
        then
          let (s4, index_mut_back1) ←
            core.slice.index.Slice.index_mut
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
              workspace.roots { «end» := count }
          let s5 ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) values
              { start := 11#usize, «end» := i }
          let s6 ← core.slice.Slice.copy_from_slice core.marker.CopyU64 s4 s5
          let product1 := index_mut_back s3
          let s7 := split_at_mut_back (values, product1)
          let s8 := index_mut_back1 s6
          ok (core.result.Result.Ok (some types.Stage.Verification),
            { self with next := (some types.Stage.Verification) },
            { workspace with polynomials := s7, roots := s8 },
            fun workspace1 => workspace1, meter1)
        else
          let i1 := Slice.len odd
          let self1 ← decode.degree_probe.DegreeProbe.reject self i1 budget1
          let product1 := index_mut_back s3
          let s4 := split_at_mut_back (values, product1)
          ok (core.result.Result.Ok self1.next, self1,
            { workspace with polynomials := s4 }, fun workspace1 => workspace1,
            meter1)
      | types.Stage.Reconstruction => fail panic
      | types.Stage.BerlekampMassey => fail panic
      | types.Stage.CandidateEvaluation => fail panic
      | types.Stage.Deflation => fail panic
      | types.Stage.ReducerPreparation => fail panic
      | types.Stage.AffinePreparation => fail panic
      | types.Stage.AffineEnumeration => fail panic
      | types.Stage.AffineSplit => fail panic
      | types.Stage.Trace => fail panic
      | types.Stage.Gcd => fail panic
      | types.Stage.FactorDivision => fail panic
      | types.Stage.Leaf => fail panic
      | types.Stage.Verification =>
        let s ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
            workspace.roots { «end» := count }
        let (b, s1) ←
          decode.probe.verified fieldBinaryFieldInst
            backendcontractBulkKernelsInst odd s workspace.verification
        if b
        then
          ok (core.result.Result.Ok (some types.Stage.Canonicalization),
            { self with next := (some types.Stage.Canonicalization) },
            { workspace with verification := s1 },
            fun workspace1 => workspace1, meter1)
        else
          let i := Slice.len odd
          let self1 ← decode.degree_probe.DegreeProbe.reject self i budget1
          ok (core.result.Result.Ok self1.next, self1,
            { workspace with verification := s1 },
            fun workspace1 => workspace1, meter1)
      | types.Stage.Canonicalization =>
        let (s, index_mut_back) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
            workspace.roots { «end» := count }
        let s1 ← core.slice.Slice.sort_unstable core.cmp.OrdU64 s
        let s2 := index_mut_back s1
        ok (core.result.Result.Ok none, { self with next := none },
          { workspace with roots := s2 }, fun workspace1 => workspace1, meter1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          (Option types.Stage) (core.convert.FromSame types.DecodeError)
          residual
      ok (r2, self, workspace, fun workspace1 => workspace1, meter1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        (Option types.Stage) (core.convert.FromSame types.DecodeError) residual
    ok (r1, self, workspace, fun workspace1 => workspace1, meter)

end bulksketch
