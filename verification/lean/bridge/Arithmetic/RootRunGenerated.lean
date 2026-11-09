-- Original checked Roots::run with the source-backed affine wrappers.
import Arithmetic.DenseGcdGenerated
import Arithmetic.DenseReducerTableGenerated
import Arithmetic.DenseReducerSquareGenerated
import Arithmetic.RootLeafGenerated
import Arithmetic.RootTraceGenerated
import Arithmetic.RootSetupGenerated
import Arithmetic.RootDivideGenerated
import Arithmetic.AffineSplitterGenerated
import Arithmetic.RootAffinePreparationGenerated
import Arithmetic.RootEnumerateGenerated

open Aeneas Aeneas.Std Result Error

namespace Aeneas.Std.RootRunRuntime

/-- Explicit lower-level calls in the two original affine wrappers. -/
structure OtherCallees where
  enumerate : RootEnumerateRuntime.Enumerate
  preparation : RootAffinePreparationRuntime.Callees

/-- Shared Option view does not change either branch or payload. -/
def optionAsRef {T : Type} (value : Option T) : Result (Option T) := .ok value

end Aeneas.Std.RootRunRuntime

namespace bulksketch

variable (calls : RootRunRuntime.OtherCallees) (division : DenseDivisionRuntime.DivRem)

local notation "core.option.Option.as_ref" => RootRunRuntime.optionAsRef
local notation "decode.affine.splitter" =>
  (decode.affine.splitter poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into)
local notation "decode.roots.Roots.divide" =>
  (decode.roots.Roots.divide (poly.Dense.Insts.BulksketchPolyPolynomial.exact_divide_into division))
local notation "decode.roots.Roots.trace" =>
  (decode.roots.Roots.trace poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into)
local notation "decode.roots.Roots.enumerate_affine" => (decode.roots.Roots.enumerate_affine calls.enumerate)
local notation "decode.roots.Roots.prepare_affine" => (decode.roots.Roots.prepare_affine calls.preparation)
local notation "poly.Dense.Insts.BulksketchPolyPolynomial.monic_gcd_into" =>
  (poly.Dense.Insts.BulksketchPolyPolynomial.monic_gcd_into division)

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::run]:
    Source: 'src/decode/roots.rs', lines 128:4-236:5 -/
def decode.roots.Roots.run
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (self : decode.roots.Roots) (stage : types.Stage)
  (workspace : decode.scratch.RowWorkspace) (meter : types.WorkMeter) :
  Result ((core.result.Result (core.result.Result types.Stage
    types.DecodeFailure) types.DecodeError) × decode.roots.Roots ×
    decode.scratch.RowWorkspace × (decode.scratch.RowWorkspace →
    decode.scratch.RowWorkspace) × types.WorkMeter)
  := do
  let b ←
    match stage with
    | types.Stage.DirectOne => ok false
    | types.Stage.DirectTwo => ok false
    | types.Stage.GuardThree => ok false
    | types.Stage.NewtonThree => ok false
    | types.Stage.GuardFour => ok false
    | types.Stage.NewtonFour => ok false
    | types.Stage.LeafThree => ok true
    | types.Stage.LeafFour => ok true
    | types.Stage.FactorVerification => ok true
    | types.Stage.Reconstruction => ok false
    | types.Stage.BerlekampMassey => ok false
    | types.Stage.CandidateEvaluation => ok false
    | types.Stage.Deflation => ok false
    | types.Stage.ReducerPreparation => ok false
    | types.Stage.AffinePreparation => ok false
    | types.Stage.AffineEnumeration => ok false
    | types.Stage.AffineSplit => ok false
    | types.Stage.Trace => ok false
    | types.Stage.Gcd => ok false
    | types.Stage.FactorDivision => ok false
    | types.Stage.Leaf => ok false
    | types.Stage.Verification => ok false
    | types.Stage.Canonicalization => ok false
  if b
  then
    decode.roots.Roots.closed_leaf fieldBinaryFieldInst
      backendcontractBulkKernelsInst self stage workspace meter
  else
    let b1 ←
      types.Stage.Insts.CoreCmpPartialEqStage.eq stage types.Stage.Leaf
    if b1
    then
      decode.roots.Roots.leaf fieldBinaryFieldInst
        backendcontractBulkKernelsInst self workspace meter
    else
      let b2 ←
        types.Stage.Insts.CoreCmpPartialEqStage.eq stage
          types.Stage.AffinePreparation
      if b2
      then
        decode.roots.Roots.prepare_affine fieldBinaryFieldInst
          backendcontractBulkKernelsInst self workspace meter
      else
        let b3 ←
          types.Stage.Insts.CoreCmpPartialEqStage.eq stage
            types.Stage.AffineEnumeration
        if b3
        then
          decode.roots.Roots.enumerate_affine fieldBinaryFieldInst
            backendcontractBulkKernelsInst self workspace meter
        else
          let (buffers, new_back) ←
            decode.roots.FactorWork.new self.degree workspace.polynomials
              workspace.square_table workspace.raw workspace.basis
          match stage with
          | types.Stage.DirectOne => fail panic
          | types.Stage.DirectTwo => fail panic
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
          | types.Stage.ReducerPreparation =>
            let (r, meter1) ←
              decode.roots.charge meter (decode.work.Charge.Table self.degree)
            let cf ← core.result.Result.Insts.CoreOpsTry.branch r
            match cf with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let (s, s1) ←
                poly.Dense.Insts.BulksketchPolyPolynomial.prepare_square_table
                  fieldBinaryFieldInst backendcontractBulkKernelsInst
                  buffers.modulus buffers.table buffers.work
              if self.affine
              then
                if self.affine_ready
                then
                  let (s2, s3, s4, sb) :=
                    new_back { buffers with work := s1, table := s }
                  ok (core.result.Result.Ok (core.result.Result.Ok
                    types.Stage.AffineSplit), self,
                    {
                      workspace
                        with
                        polynomials := s2,
                        square_table := s3,
                        raw := s4,
                        basis := sb
                    }, fun workspace1 => workspace1, meter1)
                else
                  let (s2, s3, s4, sb) :=
                    new_back { buffers with work := s1, table := s }
                  ok (core.result.Result.Ok (core.result.Result.Ok
                    types.Stage.AffinePreparation), self,
                    {
                      workspace
                        with
                        polynomials := s2,
                        square_table := s3,
                        raw := s4,
                        basis := sb
                    }, fun workspace1 => workspace1, meter1)
              else
                let (s2, s3, s4, sb) :=
                  new_back { buffers with work := s1, table := s }
                ok (core.result.Result.Ok (core.result.Result.Ok
                  types.Stage.Trace), self,
                  {
                    workspace
                      with
                      polynomials := s2,
                      square_table := s3,
                      raw := s4,
                      basis := sb
                  }, fun workspace1 => workspace1, meter1)
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r1 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  (core.result.Result types.Stage types.DecodeFailure)
                  (core.convert.FromSame types.DecodeError) residual
              let (s, s1, s2, sb) := new_back buffers
              ok (r1, self,
                {
                  workspace
                    with
                    polynomials := s,
                    square_table := s1,
                    raw := s2,
                    basis := sb
                }, fun workspace1 => workspace1, meter1)
          | types.Stage.AffinePreparation => fail panic
          | types.Stage.AffineEnumeration => fail panic
          | types.Stage.AffineSplit =>
            let (r, meter1) ←
              decode.roots.charge meter (decode.work.Charge.AffineSplit
                self.degree self.affine_rank)
            let cf ← core.result.Result.Insts.CoreOpsTry.branch r
            match cf with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              if self.affine_rank = 0#usize
              then
                let (s, s1, s2, sb) := new_back buffers
                ok (core.result.Result.Ok (core.result.Result.Err
                  types.DecodeFailure.NotSplit), self,
                  {
                    workspace
                      with
                      polynomials := s,
                      square_table := s1,
                      raw := s2,
                      basis := sb
                  }, fun workspace1 => workspace1, meter1)
              else
                let rank ← self.affine_rank - 1#usize
                let i ← self.stride * self.stride
                let i1 ← decode.affine.subspace_start rank
                let start ← i + i1
                let i2 ← start + rank
                let i3 ← i2 + 1#usize
                let s ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U64)
                    workspace.factors { start, «end» := i3 }
                let (i4, s1, s2, s3) ←
                  decode.affine.splitter fieldBinaryFieldInst
                    backendcontractBulkKernelsInst buffers.modulus
                    buffers.table s self.affine_base buffers.trace buffers.work
                    buffers.raw
                let (s4, s5, s6, sb) :=
                  new_back { buffers with trace := s1, work := s2, raw := s3 }
                ok (core.result.Result.Ok (core.result.Result.Ok
                  types.Stage.Gcd), { self with trace_len := i4 },
                  {
                    workspace
                      with
                      polynomials := s4,
                      square_table := s5,
                      raw := s6,
                      basis := sb
                  }, fun workspace1 => workspace1, meter1)
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r1 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  (core.result.Result types.Stage types.DecodeFailure)
                  (core.convert.FromSame types.DecodeError) residual
              let (s, s1, s2, sb) := new_back buffers
              ok (r1, self,
                {
                  workspace
                    with
                    polynomials := s,
                    square_table := s1,
                    raw := s2,
                    basis := sb
                }, fun workspace1 => workspace1, meter1)
          | types.Stage.Trace =>
            let (r, self1, fw, trace_back, meter1) ←
              decode.roots.Roots.trace fieldBinaryFieldInst
                backendcontractBulkKernelsInst self buffers meter
            let (s, s1, s2, sb) := new_back (trace_back fw)
            ok (r, self1,
              {
                workspace
                  with
                  polynomials := s, square_table := s1, raw := s2, basis := sb
              }, fun workspace1 => workspace1, meter1)
          | types.Stage.Gcd =>
            let (r, meter1) ←
              decode.roots.charge meter (decode.work.Charge.Gcd self.degree)
            let cf ← core.result.Result.Insts.CoreOpsTry.branch r
            match cf with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let s ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                  buffers.trace { «end» := self.trace_len }
              let (i, s1, s2, s3) ←
                poly.Dense.Insts.BulksketchPolyPolynomial.monic_gcd_into
                  fieldBinaryFieldInst backendcontractBulkKernelsInst
                  buffers.modulus s buffers.gcd buffers.work buffers.raw
              let i1 ← i - 1#usize
              if i1 > 0#usize
              then
                if i1 < self.degree
                then
                  let (s4, s5, s6, sb) :=
                    new_back { buffers with gcd := s1, work := s2, raw := s3 }
                  ok (core.result.Result.Ok (core.result.Result.Ok
                    types.Stage.FactorDivision),
                    { self with gcd_len := i, gcd_degree := i1 },
                    {
                      workspace
                        with
                        polynomials := s4,
                        square_table := s5,
                        raw := s6,
                        basis := sb
                    }, fun workspace1 => workspace1, meter1)
                else
                  if self.affine
                  then
                    let i2 ← self.affine_rank - 1#usize
                    if i = 1#usize
                    then
                      let o ←
                        core.option.Option.as_ref buffers.basis.directions
                      let a ←
                        core.option.Option.expect o (toStr "affine basis")
                      let i3 ← Array.index_usize a i2
                      let i4 ← lift (self.affine_base ^^^ i3)
                      let (s4, s5, s6, sb) :=
                        new_back
                          { buffers with gcd := s1, work := s2, raw := s3 }
                      ok (core.result.Result.Ok (core.result.Result.Ok
                        types.Stage.AffineSplit),
                        {
                          self
                            with
                            gcd_len := i,
                            gcd_degree := i1,
                            affine_base := i4,
                            affine_rank := i2
                        },
                        {
                          workspace
                            with
                            polynomials := s4,
                            square_table := s5,
                            raw := s6,
                            basis := sb
                        }, fun workspace1 => workspace1, meter1)
                    else
                      let (s4, s5, s6, sb) :=
                        new_back
                          { buffers with gcd := s1, work := s2, raw := s3 }
                      ok (core.result.Result.Ok (core.result.Result.Ok
                        types.Stage.AffineSplit),
                        {
                          self
                            with
                            gcd_len := i, gcd_degree := i1, affine_rank := i2
                        },
                        {
                          workspace
                            with
                            polynomials := s4,
                            square_table := s5,
                            raw := s6,
                            basis := sb
                        }, fun workspace1 => workspace1, meter1)
                  else
                    let i2 ← self.direction + 1#u32
                    let i3 ← fieldBinaryFieldInst.BITS
                    if i2 = i3
                    then
                      let (s4, s5, s6, sb) :=
                        new_back
                          { buffers with gcd := s1, work := s2, raw := s3 }
                      ok (core.result.Result.Ok (core.result.Result.Err
                        types.DecodeFailure.NotSplit),
                        {
                          self
                            with
                            direction := i2, gcd_len := i, gcd_degree := i1
                        },
                        {
                          workspace
                            with
                            polynomials := s4,
                            square_table := s5,
                            raw := s6,
                            basis := sb
                        }, fun workspace1 => workspace1, meter1)
                    else
                      let (s4, s5, s6, sb) :=
                        new_back
                          { buffers with gcd := s1, work := s2, raw := s3 }
                      ok (core.result.Result.Ok (core.result.Result.Ok
                        types.Stage.Trace),
                        {
                          self
                            with
                            direction := i2, gcd_len := i, gcd_degree := i1
                        },
                        {
                          workspace
                            with
                            polynomials := s4,
                            square_table := s5,
                            raw := s6,
                            basis := sb
                        }, fun workspace1 => workspace1, meter1)
              else
                if self.affine
                then
                  let i2 ← self.affine_rank - 1#usize
                  if i = 1#usize
                  then
                    let o ←
                      core.option.Option.as_ref buffers.basis.directions
                    let a ←
                      core.option.Option.expect o (toStr "affine basis")
                    let i3 ← Array.index_usize a i2
                    let i4 ← lift (self.affine_base ^^^ i3)
                    let (s4, s5, s6, sb) :=
                      new_back
                        { buffers with gcd := s1, work := s2, raw := s3 }
                    ok (core.result.Result.Ok (core.result.Result.Ok
                      types.Stage.AffineSplit),
                      {
                        self
                          with
                          gcd_len := i,
                          gcd_degree := i1,
                          affine_base := i4,
                          affine_rank := i2
                      },
                      {
                        workspace
                          with
                          polynomials := s4,
                          square_table := s5,
                          raw := s6,
                          basis := sb
                      }, fun workspace1 => workspace1, meter1)
                  else
                    let (s4, s5, s6, sb) :=
                      new_back
                        { buffers with gcd := s1, work := s2, raw := s3 }
                    ok (core.result.Result.Ok (core.result.Result.Ok
                      types.Stage.AffineSplit),
                      {
                        self
                          with
                          gcd_len := i, gcd_degree := i1, affine_rank := i2
                      },
                      {
                        workspace
                          with
                          polynomials := s4,
                          square_table := s5,
                          raw := s6,
                          basis := sb
                      }, fun workspace1 => workspace1, meter1)
                else
                  let i2 ← self.direction + 1#u32
                  let i3 ← fieldBinaryFieldInst.BITS
                  if i2 = i3
                  then
                    let (s4, s5, s6, sb) :=
                      new_back
                        { buffers with gcd := s1, work := s2, raw := s3 }
                    ok (core.result.Result.Ok (core.result.Result.Err
                      types.DecodeFailure.NotSplit),
                      {
                        self
                          with
                          direction := i2, gcd_len := i, gcd_degree := i1
                      },
                      {
                        workspace
                          with
                          polynomials := s4,
                          square_table := s5,
                          raw := s6,
                          basis := sb
                      }, fun workspace1 => workspace1, meter1)
                  else
                    let (s4, s5, s6, sb) :=
                      new_back
                        { buffers with gcd := s1, work := s2, raw := s3 }
                    ok (core.result.Result.Ok (core.result.Result.Ok
                      types.Stage.Trace),
                      {
                        self
                          with
                          direction := i2, gcd_len := i, gcd_degree := i1
                      },
                      {
                        workspace
                          with
                          polynomials := s4,
                          square_table := s5,
                          raw := s6,
                          basis := sb
                      }, fun workspace1 => workspace1, meter1)
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r1 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  (core.result.Result types.Stage types.DecodeFailure)
                  (core.convert.FromSame types.DecodeError) residual
              let (s, s1, s2, sb) := new_back buffers
              ok (r1, self,
                {
                  workspace
                    with
                    polynomials := s,
                    square_table := s1,
                    raw := s2,
                    basis := sb
                }, fun workspace1 => workspace1, meter1)
          | types.Stage.FactorDivision =>
            let (r, self1, fw, divide_back, s, s1, meter1) ←
              decode.roots.Roots.divide fieldBinaryFieldInst
                backendcontractBulkKernelsInst self buffers workspace.factors
                workspace.stack meter
            let (s2, s3, s4, sb) := new_back (divide_back fw)
            ok (r, self1,
              {
                workspace
                  with
                  polynomials := s2,
                  factors := s,
                  square_table := s3,
                  raw := s4,
                  stack := s1,
                  basis := sb
              }, fun workspace1 => workspace1, meter1)
          | types.Stage.Leaf => fail panic
          | types.Stage.Verification => fail panic
          | types.Stage.Canonicalization => fail panic

end bulksketch
