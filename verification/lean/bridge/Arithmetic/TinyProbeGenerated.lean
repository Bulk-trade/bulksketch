-- Original checked tiny probe and backend wrapper.
import Arithmetic.RowDispatchGenerated
import Arithmetic.CanonicalizeGenerated
import Arithmetic.ReconstructionRuntime
import Arithmetic.DegreeProbeGenerated
import Arithmetic.DirectTwoGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace bulksketch

local notation "core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all" =>
  ReconstructionRuntime.sliceAll
local notation "core.slice.Slice.windows" => CanonicalizeRuntime.windows
local notation "core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice" =>
  (fun (_ : Type) => ())
local notation "core.iter.traits.iterator.Iterator.any.default" => CanonicalizeRuntime.anyWindows

/-- [bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::run_charged::{closure#1}]
    Source: 'src/decode/probe.rs', lines 141:45-141:61 -/
@[reducible]
def decode.probe.Probe.run_charged.closure_1 (F : Type _) (K : Type _) := Unit

/-- [bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::run_charged::{closure}]
    Source: 'src/decode/probe.rs', lines 140:40-140:75 -/
@[reducible]
def decode.probe.Probe.run_charged.closure (F : Type _) (K : Type _) := Unit

/-- [bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::run_charged::{impl core::ops::function::FnMut<(&'_0 [u64],), bool> for bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::run_charged::{closure#1}<'_0, F, K>}::call_mut]:
    Source: 'src/decode/probe.rs', lines 141:45-141:61 -/
def
  decode.probe.Probe.run_charged.closure_1.Insts.CoreOpsFunctionFnMutTupleShared0SliceU64Bool.call_mut
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.probe.Probe.run_charged.closure_1 F K)
  (tupled_args : Slice Std.U64) :
  Result (Bool × (decode.probe.Probe.run_charged.closure_1 F K))
  := do
  let i ← Slice.index_usize tupled_args 0#usize
  let i1 ← Slice.index_usize tupled_args 1#usize
  ok (i = i1, ())

/-- [bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::run_charged::{impl core::ops::function::FnOnce<(&'_0 [u64],), bool> for bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::run_charged::{closure#1}<'_0, F, K>}::call_once]:
    Source: 'src/decode/probe.rs', lines 141:45-141:61 -/
def
  decode.probe.Probe.run_charged.closure_1.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU64Bool.call_once
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.probe.Probe.run_charged.closure_1 F K) (s : Slice Std.U64) :
  Result Bool
  := do
  let (b, _) ←
    decode.probe.Probe.run_charged.closure_1.Insts.CoreOpsFunctionFnMutTupleShared0SliceU64Bool.call_mut
      fieldBinaryFieldInst backendcontractBulkKernelsInst () s
  ok b

/-- Trait implementation: [bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::run_charged::{impl core::ops::function::FnOnce<(&'_0 [u64],), bool> for bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::run_charged::{closure#1}<'_0, F, K>}]
    Source: 'src/decode/probe.rs', lines 141:45-141:61 -/
@[reducible]
def
  decode.probe.Probe.run_charged.closure_1.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU64Bool
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnOnce (decode.probe.Probe.run_charged.closure_1 F K)
  (Slice Std.U64) Bool := {
  call_once :=
    decode.probe.Probe.run_charged.closure_1.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU64Bool.call_once
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- Trait implementation: [bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::run_charged::{impl core::ops::function::FnMut<(&'_0 [u64],), bool> for bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::run_charged::{closure#1}<'_0, F, K>}]
    Source: 'src/decode/probe.rs', lines 141:45-141:61 -/
@[reducible]
def
  decode.probe.Probe.run_charged.closure_1.Insts.CoreOpsFunctionFnMutTupleShared0SliceU64Bool
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnMut (decode.probe.Probe.run_charged.closure_1 F K) (Slice
  Std.U64) Bool := {
  FnOnceInst :=
    decode.probe.Probe.run_charged.closure_1.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU64Bool
    fieldBinaryFieldInst backendcontractBulkKernelsInst
  call_mut :=
    decode.probe.Probe.run_charged.closure_1.Insts.CoreOpsFunctionFnMutTupleShared0SliceU64Bool.call_mut
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- [bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::run_charged::{impl core::ops::function::FnMut<(&'_0 u64,), bool> for bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::run_charged::{closure}<'_0, F, K>}::call_mut]:
    Source: 'src/decode/probe.rs', lines 140:40-140:75 -/
def
  decode.probe.Probe.run_charged.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool.call_mut
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.probe.Probe.run_charged.closure F K) (tupled_args : Std.U64) :
  Result (Bool × (decode.probe.Probe.run_charged.closure F K))
  := do
  if tupled_args != 0#u64
  then
    let i ← fieldBinaryFieldInst.MASK
    let i1 ← lift (~~~ i)
    let i2 ← lift (tupled_args &&& i1)
    ok (i2 = 0#u64, ())
  else ok (false, ())

/-- [bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::run_charged::{impl core::ops::function::FnOnce<(&'_0 u64,), bool> for bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::run_charged::{closure}<'_0, F, K>}::call_once]:
    Source: 'src/decode/probe.rs', lines 140:40-140:75 -/
def
  decode.probe.Probe.run_charged.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U64Bool.call_once
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.probe.Probe.run_charged.closure F K) (i : Std.U64) :
  Result Bool
  := do
  let (b, _) ←
    decode.probe.Probe.run_charged.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool.call_mut
      fieldBinaryFieldInst backendcontractBulkKernelsInst () i
  ok b

/-- Trait implementation: [bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::run_charged::{impl core::ops::function::FnOnce<(&'_0 u64,), bool> for bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::run_charged::{closure}<'_0, F, K>}]
    Source: 'src/decode/probe.rs', lines 140:40-140:75 -/
@[reducible]
def
  decode.probe.Probe.run_charged.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U64Bool
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnOnce (decode.probe.Probe.run_charged.closure F K) Std.U64
  Bool := {
  call_once :=
    decode.probe.Probe.run_charged.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U64Bool.call_once
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- Trait implementation: [bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::run_charged::{impl core::ops::function::FnMut<(&'_0 u64,), bool> for bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::run_charged::{closure}<'_0, F, K>}]
    Source: 'src/decode/probe.rs', lines 140:40-140:75 -/
@[reducible]
def
  decode.probe.Probe.run_charged.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnMut (decode.probe.Probe.run_charged.closure F K) Std.U64
  Bool := {
  FnOnceInst :=
    decode.probe.Probe.run_charged.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U64Bool
    fieldBinaryFieldInst backendcontractBulkKernelsInst
  call_mut :=
    decode.probe.Probe.run_charged.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool.call_mut
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- [bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::run_charged]:
    Source: 'src/decode/probe.rs', lines 106:4-164:5 -/
def decode.probe.Probe.run_charged
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (self : decode.probe.Probe) (difference : Slice Std.U64)
  (verification : Slice Std.U64) (roots : Slice Std.U64) :
  Result (decode.row.RowProgress × decode.probe.Probe × (Slice Std.U64) ×
    (Slice Std.U64))
  := do
  let stage ← core.option.Option.expect self.next (toStr "charged probe")
  match stage with
  | types.Stage.DirectOne =>
    let i ← Slice.index_usize difference 0#usize
    let roots1 ← Slice.update roots 0#usize i
    ok
      ({
         stage := types.Stage.DirectOne,
         locator_degree := 0#usize,
         candidate_hits := 0#usize,
         trace_attempts := 0#usize,
         gcd_degree := 0#usize
       },
      { self with next := (some types.Stage.Verification), count := 1#usize },
      verification, roots1)
  | types.Stage.DirectTwo =>
    let i ← Slice.index_usize difference 0#usize
    let i1 ← Slice.index_usize difference 1#usize
    let o ←
      decode.direct.two fieldBinaryFieldInst backendcontractBulkKernelsInst i
        i1
    match o with
    | none =>
      let i2 := Slice.len difference
      let self1 ← decode.probe.Probe.reject self i2
      ok
        ({
           stage := types.Stage.DirectTwo,
           locator_degree := 0#usize,
           candidate_hits := 0#usize,
           trace_attempts := 0#usize,
           gcd_degree := 0#usize
         }, self1, verification, roots)
    | some pair =>
      let (s, index_mut_back) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) roots
          { «end» := 2#usize }
      let s1 ← lift (Array.to_slice pair.roots)
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU64 s s1
      let roots1 := index_mut_back s2
      ok
        ({
           stage := types.Stage.DirectTwo,
           locator_degree := 0#usize,
           candidate_hits := 0#usize,
           trace_attempts := 0#usize,
           gcd_degree := 0#usize
         },
        { self with next := (some types.Stage.Verification), count := 2#usize },
        verification, roots1)
  | types.Stage.GuardThree => fail panic
  | types.Stage.NewtonThree => fail panic
  | types.Stage.GuardFour => fail panic
  | types.Stage.NewtonFour => fail panic
  | types.Stage.LeafThree => fail panic
  | types.Stage.LeafFour => fail panic
  | types.Stage.FactorVerification => fail panic
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
    let roots1 ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) roots
        { «end» := self.count }
    let i := Slice.len roots1
    if i <= self.budget.nonzero
    then
      let i1 ← core.slice.Slice.iter roots1
      let (b, _) ←
        core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all
          (decode.probe.Probe.run_charged.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool
          fieldBinaryFieldInst backendcontractBulkKernelsInst) i1 ()
      if b
      then
        let w ← core.slice.Slice.windows roots1 2#usize
        let (b1, _) ←
          core.iter.traits.iterator.Iterator.any.default
            (core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice
            Std.U64)
            (decode.probe.Probe.run_charged.closure_1.Insts.CoreOpsFunctionFnMutTupleShared0SliceU64Bool
            fieldBinaryFieldInst backendcontractBulkKernelsInst) w ()
        if b1
        then
          let i2 := Slice.len difference
          let self1 ← decode.probe.Probe.reject self i2
          ok
            ({
               stage := types.Stage.Verification,
               locator_degree := 0#usize,
               candidate_hits := 0#usize,
               trace_attempts := 0#usize,
               gcd_degree := 0#usize
             }, self1, verification, roots)
        else
          let (b2, verification1) ←
            decode.probe.verified fieldBinaryFieldInst
              backendcontractBulkKernelsInst difference roots1 verification
          if b2
          then
            ok
              ({
                 stage := types.Stage.Verification,
                 locator_degree := 0#usize,
                 candidate_hits := 0#usize,
                 trace_attempts := 0#usize,
                 gcd_degree := 0#usize
               }, { self with next := (some types.Stage.Canonicalization) },
              verification1, roots)
          else
            let i2 := Slice.len difference
            let self1 ← decode.probe.Probe.reject self i2
            ok
              ({
                 stage := types.Stage.Verification,
                 locator_degree := 0#usize,
                 candidate_hits := 0#usize,
                 trace_attempts := 0#usize,
                 gcd_degree := 0#usize
               }, self1, verification1, roots)
      else
        let i2 := Slice.len difference
        let self1 ← decode.probe.Probe.reject self i2
        ok
          ({
             stage := types.Stage.Verification,
             locator_degree := 0#usize,
             candidate_hits := 0#usize,
             trace_attempts := 0#usize,
             gcd_degree := 0#usize
           }, self1, verification, roots)
    else
      let i1 := Slice.len difference
      let self1 ← decode.probe.Probe.reject self i1
      ok
        ({
           stage := types.Stage.Verification,
           locator_degree := 0#usize,
           candidate_hits := 0#usize,
           trace_attempts := 0#usize,
           gcd_degree := 0#usize
         }, self1, verification, roots)
  | types.Stage.Canonicalization =>
    if self.count = 2#usize
    then
      let i ← Slice.index_usize roots 0#usize
      let i1 ← Slice.index_usize roots 1#usize
      if i > i1
      then
        let roots1 ← core.slice.Slice.swap roots 0#usize 1#usize
        ok
          ({
             stage := types.Stage.Canonicalization,
             locator_degree := 0#usize,
             candidate_hits := 0#usize,
             trace_attempts := 0#usize,
             gcd_degree := 0#usize
           }, { self with next := none }, verification, roots1)
      else
        ok
          ({
             stage := types.Stage.Canonicalization,
             locator_degree := 0#usize,
             candidate_hits := 0#usize,
             trace_attempts := 0#usize,
             gcd_degree := 0#usize
           }, { self with next := none }, verification, roots)
    else
      ok
        ({
           stage := types.Stage.Canonicalization,
           locator_degree := 0#usize,
           candidate_hits := 0#usize,
           trace_attempts := 0#usize,
           gcd_degree := 0#usize
         }, { self with next := none }, verification, roots)

/-- [bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::charge]:
    Source: 'src/decode/probe.rs', lines 83:4-103:5 -/
def decode.probe.Probe.charge
  (self : decode.probe.Probe) (capacity : Std.Usize) (meter : types.WorkMeter)
  :
  Result ((core.result.Result Unit types.DecodeError) × types.WorkMeter)
  := do
  let stage ← core.option.Option.expect self.next (toStr "active probe")
  let charge ←
    match stage with
    | types.Stage.DirectOne => ok decode.work.Charge.DirectOne
    | types.Stage.DirectTwo => ok decode.work.Charge.DirectTwo
    | types.Stage.GuardThree => fail panic
    | types.Stage.NewtonThree => fail panic
    | types.Stage.GuardFour => fail panic
    | types.Stage.NewtonFour => fail panic
    | types.Stage.LeafThree => fail panic
    | types.Stage.LeafFour => fail panic
    | types.Stage.FactorVerification => fail panic
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
      ok (decode.work.Charge.Verify capacity self.budget.total)
    | types.Stage.Canonicalization =>
      ok (decode.work.Charge.Canonicalize self.budget.total)
  let r ← decode.work.WorkScheduleV1.cost charge
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (r1, meter1) ← types.WorkMeter.charge meter val
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      ok (core.result.Result.Ok (), meter1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame types.DecodeError) residual
      ok (r2, meter1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame types.DecodeError) residual
    ok (r1, meter)

/-- [bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::run_next]:
    Source: 'src/decode/probe.rs', lines 69:4-78:5 -/
def decode.probe.Probe.run_next
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (self : decode.probe.Probe) (difference : Slice Std.U64)
  (verification : Slice Std.U64) (roots : Slice Std.U64)
  (meter : types.WorkMeter) :
  Result ((core.result.Result decode.row.RowProgress types.DecodeError) ×
    decode.probe.Probe × (Slice Std.U64) × (Slice Std.U64) ×
    types.WorkMeter)
  := do
  let i := Slice.len difference
  let (r, meter1) ← decode.probe.Probe.charge self i meter
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let (rp, self1, verification1, roots1) ←
      decode.probe.Probe.run_charged fieldBinaryFieldInst
        backendcontractBulkKernelsInst self difference verification roots
    ok (core.result.Result.Ok rp, self1, verification1, roots1, meter1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        decode.row.RowProgress (core.convert.FromSame types.DecodeError)
        residual
    ok (r1, self, verification, roots, meter1)

variable (dictionaries : RowDispatchRuntime.Dictionaries)
local notation "backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels" => dictionaries.portable
local notation "backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels" => dictionaries.pclmul
local notation "backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels" => dictionaries.vpclmul512

/-- [bulksketch::sketch::dispatch::run_probe]:
    Source: 'src/sketch/dispatch.rs', lines 224:0-244:1 -/
def sketch.dispatch.run_probe
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backend : types.BackendId) (probe : decode.probe.Probe)
  (difference : Slice Std.U64) (verification : Slice Std.U64)
  (roots : Slice Std.U64) (meter : types.WorkMeter) :
  Result ((core.result.Result decode.row.RowProgress types.DecodeError) ×
    decode.probe.Probe × (Slice Std.U64) × (Slice Std.U64) ×
    types.WorkMeter)
  := do
  match backend with
  | types.BackendId.Portable =>
    decode.probe.Probe.run_next fieldBinaryFieldInst
      (backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels
      fieldBinaryFieldInst) probe difference verification roots meter
  | types.BackendId.Pclmul =>
    decode.probe.Probe.run_next fieldBinaryFieldInst
      (backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels
      fieldBinaryFieldInst) probe difference verification roots meter
  | types.BackendId.Vpclmul256 => fail panic
  | types.BackendId.Vpclmul512 =>
    decode.probe.Probe.run_next fieldBinaryFieldInst
      (backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels
      fieldBinaryFieldInst) probe difference verification roots meter

end bulksketch
