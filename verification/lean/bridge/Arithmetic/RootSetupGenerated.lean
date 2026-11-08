-- Original checked root setup declarations with scoped library bindings.
import Arithmetic.ClosedLeafGenerated
import Arithmetic.VerifyDispatchRuntime

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxRecDepth 2048

namespace bulksketch

local notation "core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice" =>
  RebuiltLfsrRuntime.inclusive

/-- [bulksketch::decode::roots::FactorWork]
    Source: 'src/decode/roots.rs', lines 39:0-47:1 -/
structure decode.roots.FactorWork where
  modulus : Slice Std.U64
  trace : Slice Std.U64
  gcd : Slice Std.U64
  work : Slice Std.U64
  table : Slice Std.U64
  raw : Slice types.RawProduct
  basis : decode.scratch.SplitterBasis

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::FactorWork<'a>}::new]:
    Source: 'src/decode/roots.rs', lines 49:4-68:5 -/
def decode.roots.FactorWork.new
  (degree : Std.Usize) (polynomials : Slice Std.U64) (table : Slice Std.U64)
  (raw : Slice types.RawProduct) (basis : decode.scratch.SplitterBasis) :
  Result (decode.roots.FactorWork × (decode.roots.FactorWork → ((Slice
    Std.U64) × (Slice Std.U64) × (Slice types.RawProduct) ×
    decode.scratch.SplitterBasis)))
  := do
  let i ← degree + 1#usize
  let ((modulus, rest), split_at_mut_back) ←
    core.slice.Slice.split_at_mut polynomials i
  let ((trace, rest1), split_at_mut_back1) ←
    core.slice.Slice.split_at_mut rest degree
  let ((gcd, work), split_at_mut_back2) ←
    core.slice.Slice.split_at_mut rest1 i
  let i1 ← degree / 2#usize
  let i2 ← degree * i1
  let (s, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) table
      { «end» := i2 }
  let back :=
    fun fw =>
      let rest2 := split_at_mut_back2 (fw.gcd, fw.work)
      let rest3 := split_at_mut_back1 (fw.trace, rest2)
      let polynomials1 := split_at_mut_back (fw.modulus, rest3)
      let table1 := index_mut_back fw.table
      (polynomials1, table1, fw.raw, fw.basis)
  ok ({ modulus, trace, gcd, work, table := s, raw, basis }, back)

/-- [bulksketch::decode::affine::square_products]:
    Source: 'src/decode/affine.rs', lines 22:0-24:1 -/
def decode.affine.square_products (degree : Std.U64) : Result Std.U64 := do
  let i ← 3#u64 * degree
  let i1 ← degree / 2#u64
  let i2 ← 2#u64 * i1
  let i3 ← core.num.U64.div_ceil degree 8#u64
  let i4 ← i2 * i3
  i + i4

/-- [bulksketch::decode::affine::predicted_affine]: loop body 1:
    Source: 'src/decode/affine.rs', lines 37:8-40:9 -/
@[rust_loop_body]
def decode.affine.predicted_affine_loop0_loop0.body
  (d : Std.U64) (column : Std.U64) (gaussian : Std.U64) (pivot : Std.U64) :
  Result (ControlFlow (Std.U64 × Std.U64) Std.U64)
  := do
  if pivot < column
  then
    let i ← d - pivot
    let i1 ← core.num.U64.div_ceil i 8#u64
    let i2 ← column + 1#u64
    let i3 ← core.num.U64.div_ceil i2 8#u64
    let i4 ← i1 + i3
    let i5 ← 2#u64 * i4
    let gaussian1 ← gaussian + i5
    let pivot1 ← pivot + 1#u64
    ok (cont (gaussian1, pivot1))
  else ok (done gaussian)

/-- [bulksketch::decode::affine::predicted_affine]: loop 1:
    Source: 'src/decode/affine.rs', lines 37:8-40:9 -/
@[rust_loop]
def decode.affine.predicted_affine_loop0_loop0
  (d : Std.U64) (gaussian : Std.U64) (column : Std.U64) (pivot : Std.U64) :
  Result Std.U64
  := do
  loop
    (fun (gaussian1, pivot1) => decode.affine.predicted_affine_loop0_loop0.body
      d column gaussian1 pivot1)
    (gaussian, pivot)

/-- [bulksketch::decode::affine::predicted_affine]: loop body 0:
    Source: 'src/decode/affine.rs', lines 35:4-42:5 -/
@[rust_loop_body]
def decode.affine.predicted_affine_loop0.body
  (d : Std.U64) (gaussian : Std.U64) (column : Std.U64) :
  Result (ControlFlow (Std.U64 × Std.U64) Std.U64)
  := do
  if column <= d
  then
    let gaussian1 ←
      decode.affine.predicted_affine_loop0_loop0 d gaussian column 0#u64
    let column1 ← column + 1#u64
    ok (cont (gaussian1, column1))
  else ok (done gaussian)

/-- [bulksketch::decode::affine::predicted_affine]: loop 0:
    Source: 'src/decode/affine.rs', lines 35:4-42:5 -/
@[rust_loop]
def decode.affine.predicted_affine_loop0
  (d : Std.U64) (gaussian : Std.U64) (column : Std.U64) : Result Std.U64 := do
  loop
    (fun (gaussian1, column1) => decode.affine.predicted_affine_loop0.body d
      gaussian1 column1)
    (gaussian, column)

/-- [bulksketch::decode::affine::predicted_affine]:
    Source: 'src/decode/affine.rs', lines 26:0-48:1 -/
def decode.affine.predicted_affine (degree : Std.Usize) : Result Bool := do
  if degree < 3#usize
  then ok false
  else
    if degree >= 64#usize
    then ok false
    else
      let d ← lift (UScalar.cast .U64 degree)
      let i ← degree - 1#usize
      let i1 ← lift (core.num.Usize.leading_zeros i)
      let i2 ← core.num.Usize.BITS - i1
      let i3 ← lift (UScalar.cast .U64 i2)
      let unit_columns ← 1#u64 + i3
      let pivots ← lift (core.num.U64.saturating_sub d unit_columns)
      let gaussian ←
        decode.affine.predicted_affine_loop0 d 0#u64 unit_columns
      let i4 ← 3#u64 * d
      let i5 ← d + 1#u64
      let normalization ← i4 * i5
      let inverses ← 28#u64 * pivots
      let map ← 16#u64 * d
      let i6 ← 6#u64 * d
      let i7 ← d - 1#u64
      let subspaces ← i6 * i7
      let i8 ← gaussian + normalization
      let i9 ← i8 + inverses
      let i10 ← i9 + map
      let i11 ← i10 + subspaces
      let i12 ← 64#u64 - d
      let i13 ← decode.affine.square_products d
      let i14 ← i12 * i13
      ok (i11 < i14)

/-- [bulksketch::decode::affine::PREFERRED_MASK]: loop body 0:
    Source: 'src/decode/affine.rs', lines 55:4-60:5 -/
@[rust_loop_body]
def decode.affine.PREFERRED_MASK_loop.body
  (degree : Std.Usize) (mask : Std.U64) :
  Result (ControlFlow (Std.Usize × Std.U64) Std.U64)
  := do
  if degree < 64#usize
  then
    let b ← decode.affine.predicted_affine degree
    let mask1 ←
      if b
      then do
           let i ← 1#u64 <<< degree
           ok (mask ||| i)
      else ok mask
    let degree1 ← degree + 1#usize
    ok (cont (degree1, mask1))
  else ok (done mask)

/-- [bulksketch::decode::affine::PREFERRED_MASK]: loop 0:
    Source: 'src/decode/affine.rs', lines 55:4-60:5 -/
@[rust_loop]
def decode.affine.PREFERRED_MASK_loop
  (degree : Std.Usize) (mask : Std.U64) : Result Std.U64 := do
  loop
    (fun (degree1, mask1) => decode.affine.PREFERRED_MASK_loop.body degree1
      mask1)
    (degree, mask)

/-- [bulksketch::decode::affine::PREFERRED_MASK]
    Source: 'src/decode/affine.rs', lines 52:0-62:2 -/
@[global_simps, irreducible]
def decode.affine.PREFERRED_MASK : Result Std.U64 :=
  decode.affine.PREFERRED_MASK_loop 3#usize 0#u64

/-- [bulksketch::decode::affine::preferred]:
    Source: 'src/decode/affine.rs', lines 64:0-66:1 -/
def decode.affine.preferred
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (degree : Std.Usize) :
  Result Bool
  := do
  let i ← fieldBinaryFieldInst.BITS
  let i1 ← lift (UScalar.cast .Usize i)
  if degree < i1
  then
    if degree < 64#usize
    then
      let i2 ← 1#u64 <<< degree
      let i3 ← decode.affine.PREFERRED_MASK
      let i4 ← lift (i3 &&& i2)
      ok (i4 != 0#u64)
    else ok false
  else ok false

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::enable_v3]:
    Source: 'src/decode/roots.rs', lines 74:4-76:5 -/
def decode.roots.Roots.enable_v3
  (self : decode.roots.Roots) : Result decode.roots.Roots := do
  ok { self with v3 := true }

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::enable_closed_form]:
    Source: 'src/decode/roots.rs', lines 78:4-80:5 -/
def decode.roots.Roots.enable_closed_form
  (self : decode.roots.Roots) : Result decode.roots.Roots := do
  ok { self with closed_form := true }

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::set_splitter_seed]:
    Source: 'src/decode/roots.rs', lines 82:4-84:5 -/
def decode.roots.Roots.set_splitter_seed
  (self : decode.roots.Roots) (seed : Std.U64) :
  Result decode.roots.Roots
  := do
  ok { self with splitter_seed := seed }

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::start]:
    Source: 'src/decode/roots.rs', lines 86:4-98:5 -/
def decode.roots.Roots.start
  (self : decode.roots.Roots) (degree : Std.Usize)
  (workspace : decode.scratch.RowWorkspace) :
  Result (types.Stage × decode.roots.Roots × decode.scratch.RowWorkspace ×
    (decode.scratch.RowWorkspace → decode.scratch.RowWorkspace))
  := do
  let i ← degree + 1#usize
  let b ←
    if self.v3
    then
      decode.affine.preferred field.Gf64.Insts.BulksketchFieldBinaryField
        degree
    else ok false
  let s ←
    if degree != 0#usize
    then
      do
      let (s1, index_mut_back) ←
        core.slice.index.Slice.index_mut
          (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
          Std.U64) workspace.polynomials { «end» := degree }
      let s2 ←
        core.slice.index.Slice.index
          (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
          Std.U64) workspace.bm { «end» := degree }
      let s3 ← core.slice.Slice.copy_from_slice core.marker.CopyU64 s1 s2
      ok (index_mut_back s3)
    else ok workspace.polynomials
  let s1 ←
    decode.roots.Roots.stage
      { self with stride := i, degree, affine := b, affine_ready := false }
  ok (s1,
    { self with stride := i, degree, affine := b, affine_ready := false },
    {
      workspace
        with
        polynomials := s, basis := { directions := none, len := 0#u32 }
    }, fun workspace1 => workspace1)

end bulksketch
