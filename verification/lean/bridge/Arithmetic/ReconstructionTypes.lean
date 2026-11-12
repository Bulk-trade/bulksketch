-- Exact declarations projected from the original reconstruction extraction.
module
public import Arithmetic.SliceKernelTypes
public import Workmeter.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
namespace bulksketch

/-- [core::marker::PhantomData]
    Source: '/rustc/library/core/src/marker.rs', lines 811:0-811:39
    Name pattern: [core::marker::PhantomData]
    Visibility: public -/
@[reducible, rust_type "core::marker::PhantomData"]
def core.marker.PhantomData (T : Type _) := Unit

/-- [bulksketch::types::Stage]
    Source: 'src/types.rs', lines 190:0-237:1
    Visibility: public -/
@[discriminant isize]
inductive types.Stage where
| DirectOne : types.Stage
| DirectTwo : types.Stage
| GuardThree : types.Stage
| NewtonThree : types.Stage
| GuardFour : types.Stage
| NewtonFour : types.Stage
| LeafThree : types.Stage
| LeafFour : types.Stage
| FactorVerification : types.Stage
| Reconstruction : types.Stage
| BerlekampMassey : types.Stage
| CandidateEvaluation : types.Stage
| Deflation : types.Stage
| ReducerPreparation : types.Stage
| AffinePreparation : types.Stage
| AffineEnumeration : types.Stage
| AffineSplit : types.Stage
| Trace : types.Stage
| Gcd : types.Stage
| FactorDivision : types.Stage
| Leaf : types.Stage
| Verification : types.Stage
| Canonicalization : types.Stage

/-- [bulksketch::decode::degree_probe::DegreeProbe]
    Source: 'src/decode/degree_probe.rs', lines 19:0-23:1 -/
structure decode.degree_probe.DegreeProbe where
  degree : Std.U8
  count : Std.U8
  next : Option types.Stage

/-- [bulksketch::decode::roots::Roots]
    Source: 'src/decode/roots.rs', lines 18:0-37:1 -/
structure decode.roots.Roots where
  pending : Std.Usize
  stride : Std.Usize
  degree : Std.Usize
  direction : Std.U32
  checked : Bool
  trace_len : Std.Usize
  gcd_len : Std.Usize
  count : Std.Usize
  attempts : Std.Usize
  gcd_degree : Std.Usize
  splitter_seed : Std.U64
  v3 : Bool
  closed_form : Bool
  solved_count : Std.Usize
  affine : Bool
  affine_ready : Bool
  affine_base : Std.U64
  affine_rank : Std.Usize

/-- [bulksketch::types::DecodeFailure]
    Source: 'src/types.rs', lines 164:0-173:1
    Visibility: public -/
@[discriminant isize]
inductive types.DecodeFailure where
| DegreeExceedsBudget : types.DecodeFailure
| InvalidLocator : types.DecodeFailure
| NotSplit : types.DecodeFailure
| VerificationFailed : types.DecodeFailure

/-- [bulksketch::decode::row::RowBudget]
    Source: 'src/decode/row.rs', lines 24:0-27:1 -/
structure decode.row.RowBudget where
  nonzero : Std.Usize
  total : Std.Usize

/-- [bulksketch::decode::row::RowInput]
    Source: 'src/decode/row.rs', lines 31:0-34:1 -/
structure decode.row.RowInput where
  difference : Slice Std.U64
  candidates : Slice Std.U64

/-- [bulksketch::decode::scratch::FactorFrame]
    Source: 'src/decode/scratch.rs', lines 21:0-26:1 -/
structure decode.scratch.FactorFrame where
  coefficient_start : Std.U64
  coefficient_len : Std.U64
  next_direction : Std.U32
  split_checked : Std.U32

/-- [bulksketch::decode::scratch::SplitterBasis]
    Source: 'src/decode/scratch.rs', lines 7:0-10:1 -/
structure decode.scratch.SplitterBasis where
  directions : Option (Array Std.U64 64#usize)
  len : Std.U32

/-- [bulksketch::decode::scratch::RowWorkspace]
    Source: 'src/decode/scratch.rs', lines 29:0-40:1 -/
structure decode.scratch.RowWorkspace where
  syndromes : Slice Std.U64
  bm : Slice Std.U64
  polynomials : Slice Std.U64
  factors : Slice Std.U64
  square_table : Slice Std.U64
  verification : Slice Std.U64
  roots : Slice Std.U64
  raw : Slice types.RawProduct
  stack : Slice decode.scratch.FactorFrame
  basis : decode.scratch.SplitterBasis

/-- [bulksketch::decode::stages::State]
    Source: 'src/decode/stages.rs', lines 28:0-33:1 -/
@[discriminant isize]
inductive decode.stages.State where
| Running : types.Stage → decode.stages.State
| Complete : decode.stages.State
| Failed : types.DecodeFailure → decode.stages.State
| Error : types.DecodeError → decode.stages.State

/-- [bulksketch::decode::stages::Execution]
    Source: 'src/decode/stages.rs', lines 36:0-53:1 -/
structure decode.stages.Execution (F : Type _) (K : Type _) where
  budget : decode.row.RowBudget
  state : decode.stages.State
  degree : Std.Usize
  hits : Std.Usize
  roots : decode.roots.Roots
  v3 : Bool
  degree_probe : Option decode.degree_probe.DegreeProbe
  marker : core.marker.PhantomData (F × K)

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::reconstruct::{closure}]
    Source: 'src/decode/stages.rs', lines 249:43-249:62 -/
@[reducible]
def decode.stages.Execution.reconstruct.closure (F : Type _) (K : Type _) :=
Unit

end bulksketch
