-- Exact original-source declaration projection. Imports and scoped external bindings are adapted only.
module
public import Arithmetic.CubicGenerated
public import Arithmetic.CertificateGenerated
public import Arithmetic.AffineQuarticRuntime
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

local notation "Shared0A.Insts.CoreCmpOrd.cmp" => Aeneas.Std.AffineQuarticRuntime.sharedCmp
local notation "core.iter.traits.iterator.Iterator.min.default" => Aeneas.Std.AffineQuarticRuntime.minimum

/-- Trait implementation: [core::cmp::impls::{impl core::cmp::Eq for &'_0 A}]
    Source: '/rustc/library/core/src/cmp.rs', lines 2525:4-2525:61
    Name pattern: [core::cmp::Eq<&'0 @A>] -/
@[reducible, rust_trait_impl "core::cmp::Eq<&'0 @A>"]
def Shared0A.Insts.CoreCmpEq {A : Type _} (EqInst : core.cmp.Eq A) :
  core.cmp.Eq A := {
  partialEqInst := core.cmp.PartialEqShared EqInst.partialEqInst
}

/-- Trait implementation: [core::cmp::impls::{impl core::cmp::Ord for &'_0 A}]
    Source: '/rustc/library/core/src/cmp.rs', lines 2514:4-2516:23
    Name pattern: [core::cmp::Ord<&'0 @A>] -/
@[reducible, rust_trait_impl "core::cmp::Ord<&'0 @A>"]
def Shared0A.Insts.CoreCmpOrd {A : Type _} (OrdInst : core.cmp.Ord A) :
  core.cmp.Ord A := {
  eqInst := Shared0A.Insts.CoreCmpEq OrdInst.eqInst
  partialOrdInst := core.cmp.PartialOrdShared OrdInst.partialOrdInst
  cmp := Shared0A.Insts.CoreCmpOrd.cmp OrdInst
}

/-- [bulksketch::decode::deg34::affine_quartic]:
    Source: 'src/decode/deg34.rs', lines 138:0-160:1 -/
def decode.deg34.affine_quartic
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (b : Std.U64) (c : Std.U64) (d : Std.U64) :
  Result (Option (Array Std.U64 4#usize))
  := do
  if c = 0#u64
  then ok none
  else
    let o ←
      decode.deg34.cubic fieldBinaryFieldInst backendcontractBulkKernelsInst
        0#u64 b c
    let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let s ←
        lift (Array.to_slice (Array.make 4#usize [ c, b, 0#u64, 1#u64 ]))
      let s1 ← lift (Array.to_slice val)
      let a := Array.repeat 4#usize 0#u64
      let (s2, _) ← lift (Array.to_slice_mut a)
      let (b1, _) ←
        decode.deg34.certificate fieldBinaryFieldInst
          backendcontractBulkKernelsInst s s1 s2
      if b1
      then
        let s3 ← lift (Array.to_slice val)
        let i ← core.slice.Slice.iter s3
        let o1 ←
          core.iter.traits.iterator.Iterator.min.default
            (core.iter.traits.iterator.IteratorSliceIter Std.U64)
            (Shared0A.Insts.CoreCmpOrd core.cmp.OrdU64) i
        let u ← core.option.Option.expect o1 (toStr "three kernel roots")
        let i1 ← backendcontractBulkKernelsInst.ArithmeticInst.square u
        let v ← lift (b ^^^ i1)
        if u = 0#u64
        then ok none
        else
          if v = 0#u64
          then ok none
          else
            let i2 ← backendcontractBulkKernelsInst.ArithmeticInst.mul u v
            if i2 != c
            then ok none
            else
              let o2 ←
                backendcontractBulkKernelsInst.ArithmeticInst.inverse c
              let cf1 ←
                core.option.Option.Insts.CoreOpsTry_traitTry.branch o2
              match cf1 with
              | core.ops.control_flow.ControlFlow.Continue val1 =>
                let i3 ←
                  backendcontractBulkKernelsInst.ArithmeticInst.mul v val1
                let iu2 ←
                  backendcontractBulkKernelsInst.ArithmeticInst.square i3
                let i4 ←
                  backendcontractBulkKernelsInst.ArithmeticInst.mul u val1
                let iv2 ←
                  backendcontractBulkKernelsInst.ArithmeticInst.square i4
                let i5 ←
                  backendcontractBulkKernelsInst.ArithmeticInst.mul d iv2
                let o3 ←
                  decode.deg34.quadratic fieldBinaryFieldInst
                    backendcontractBulkKernelsInst i5
                let cf2 ←
                  core.option.Option.Insts.CoreOpsTry_traitTry.branch o3
                match cf2 with
                | core.ops.control_flow.ControlFlow.Continue val2 =>
                  let w ←
                    backendcontractBulkKernelsInst.ArithmeticInst.mul v val2
                  let i6 ←
                    backendcontractBulkKernelsInst.ArithmeticInst.mul w iu2
                  let o4 ←
                    decode.deg34.quadratic fieldBinaryFieldInst
                      backendcontractBulkKernelsInst i6
                  let cf3 ←
                    core.option.Option.Insts.CoreOpsTry_traitTry.branch o4
                  match cf3 with
                  | core.ops.control_flow.ControlFlow.Continue val3 =>
                    let x ←
                      backendcontractBulkKernelsInst.ArithmeticInst.mul u val3
                    let i7 ← lift (w ^^^ v)
                    let i8 ←
                      backendcontractBulkKernelsInst.ArithmeticInst.mul i7 iu2
                    let o5 ←
                      decode.deg34.quadratic fieldBinaryFieldInst
                        backendcontractBulkKernelsInst i8
                    let cf4 ←
                      core.option.Option.Insts.CoreOpsTry_traitTry.branch o5
                    match cf4 with
                    | core.ops.control_flow.ControlFlow.Continue val4 =>
                      let y ←
                        backendcontractBulkKernelsInst.ArithmeticInst.mul u
                          val4
                      let i9 ← lift (x ^^^ u)
                      let i10 ← lift (y ^^^ u)
                      ok (some (Array.make 4#usize [ x, i9, y, i10 ]))
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
                        (Array Std.U64 4#usize) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
                      (Array Std.U64 4#usize) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
                    (Array Std.U64 4#usize) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
                  (Array Std.U64 4#usize) residual
      else ok none
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
        (Array Std.U64 4#usize) residual

end bulksketch
