-- Stock-checked original affine map with its native Frobenius column initializer.
import Arithmetic.AffineSubspacesGenerated
import Arithmetic.MutableZipRuntime
import Arithmetic.AffineEnumerateGenerated
import Arithmetic.TrailingZeros

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.unusedVariables false
set_option maxRecDepth 4096

namespace bulksketch

def AffineSolveMapRuntime.trailingZeros (word : U64) : Result U32 :=
  .ok ⟨word.bv.ctz.setWidth 32⟩

local notation "core.num.U64.trailing_zeros" => AffineSolveMapRuntime.trailingZeros

/-- [bulksketch::decode::affine::square_column]: loop body 0:
    Source: 'src/decode/affine.rs', lines 375:4-378:5 -/
@[rust_loop_body]
def decode.affine.square_column_loop0.body
  (word : Std.U64) (result : Std.U128) (bit : Std.I32) :
  Result (ControlFlow (Std.U128 × Std.I32) Std.U128)
  := do
  if bit < 64#i32
  then
    let i ← word >>> bit
    let i1 ← lift (i &&& 1#u64)
    let i2 ← lift (UScalar.cast .U128 i1)
    let i3 ← 2#i32 * bit
    let i4 ← i2 <<< i3
    let result1 ← lift (result ^^^ i4)
    let bit1 ← bit + 1#i32
    ok (cont (result1, bit1))
  else ok (done result)

/-- [bulksketch::decode::affine::square_column]: loop 0:
    Source: 'src/decode/affine.rs', lines 375:4-378:5 -/
@[rust_loop]
def decode.affine.square_column_loop0
  (word : Std.U64) (result : Std.U128) (bit : Std.I32) : Result Std.U128 := do
  loop
    (fun (result1, bit1) => decode.affine.square_column_loop0.body word result1
      bit1)
    (result, bit)

/-- [bulksketch::decode::affine::square_column]: loop body 1:
    Source: 'src/decode/affine.rs', lines 381:4-386:5 -/
@[rust_loop_body]
def decode.affine.square_column_loop1.body
  (polynomial : Std.U128) (result : Std.U128) (bit : Std.I32) :
  Result (ControlFlow (Std.U128 × Std.I32) Std.U128)
  := do
  if bit > 64#i32
  then
    let bit1 ← bit - 1#i32
    let i ← 1#u128 <<< bit1
    let i1 ← lift (result &&& i)
    if i1 != 0#u128
    then
      let i2 ← bit1 - 64#i32
      let i3 ← polynomial <<< i2
      let result1 ← lift (result ^^^ i3)
      ok (cont (result1, bit1))
    else ok (cont (result, bit1))
  else ok (done result)

/-- [bulksketch::decode::affine::square_column]: loop 1:
    Source: 'src/decode/affine.rs', lines 381:4-386:5 -/
@[rust_loop]
def decode.affine.square_column_loop1
  (result : Std.U128) (bit : Std.I32) (polynomial : Std.U128) :
  Result Std.U128
  := do
  loop
    (fun (result1, bit1) => decode.affine.square_column_loop1.body polynomial
      result1 bit1)
    (result, bit)

/-- [bulksketch::decode::affine::square_column]:
    Source: 'src/decode/affine.rs', lines 372:0-388:1 -/
def decode.affine.square_column (word : Std.U64) : Result Std.U64 := do
  let result ← decode.affine.square_column_loop0 word 0#u128 0#i32
  let i ← 1#u128 <<< 64#i32
  let polynomial ← lift (i ||| 27#u128)
  let result1 ← decode.affine.square_column_loop1 result 128#i32 polynomial
  ok (UScalar.cast .U64 result1)

/-- [bulksketch::decode::affine::frobenius_columns]: loop body 0:
    Source: 'src/decode/affine.rs', lines 356:4-359:5 -/
@[rust_loop_body]
def decode.affine.frobenius_columns_loop0.body
  (rows : Array (Array Std.U64 64#usize) 64#usize) (bit : Std.Usize) :
  Result (ControlFlow ((Array (Array Std.U64 64#usize) 64#usize) × Std.Usize)
    ((Array (Array Std.U64 64#usize) 64#usize) × Std.Usize))
  := do
  if bit < 64#usize
  then
    let (a, index_mut_back) ← Array.index_mut_usize rows 0#usize
    let i ← 1#u64 <<< bit
    let a1 ← Array.update a bit i
    let bit1 ← bit + 1#usize
    let a2 := index_mut_back a1
    ok (cont (a2, bit1))
  else ok (done (rows, bit))

/-- [bulksketch::decode::affine::frobenius_columns]: loop 0:
    Source: 'src/decode/affine.rs', lines 356:4-359:5 -/
@[rust_loop]
def decode.affine.frobenius_columns_loop0
  (rows : Array (Array Std.U64 64#usize) 64#usize) (bit : Std.Usize) :
  Result ((Array (Array Std.U64 64#usize) 64#usize) × Std.Usize)
  := do
  loop
    (fun (rows1, bit1) => decode.affine.frobenius_columns_loop0.body rows1
      bit1)
    (rows, bit)

/-- [bulksketch::decode::affine::frobenius_columns]: loop body 2:
    Source: 'src/decode/affine.rs', lines 363:8-366:9 -/
@[rust_loop_body]
def decode.affine.frobenius_columns_loop1_loop0.body
  (power : Std.Usize) (rows : Array (Array Std.U64 64#usize) 64#usize)
  (bit : Std.Usize) :
  Result (ControlFlow ((Array (Array Std.U64 64#usize) 64#usize) × Std.Usize)
    ((Array (Array Std.U64 64#usize) 64#usize) × Std.Usize))
  := do
  if bit < 64#usize
  then
    let i ← power - 1#usize
    let a ← Array.index_usize rows i
    let i1 ← Array.index_usize a bit
    let i2 ← decode.affine.square_column i1
    let (a1, index_mut_back) ← Array.index_mut_usize rows power
    let a2 ← Array.update a1 bit i2
    let bit1 ← bit + 1#usize
    let a3 := index_mut_back a2
    ok (cont (a3, bit1))
  else ok (done (rows, bit))

/-- [bulksketch::decode::affine::frobenius_columns]: loop 2:
    Source: 'src/decode/affine.rs', lines 363:8-366:9 -/
@[rust_loop]
def decode.affine.frobenius_columns_loop1_loop0
  (rows : Array (Array Std.U64 64#usize) 64#usize) (bit : Std.Usize)
  (power : Std.Usize) :
  Result ((Array (Array Std.U64 64#usize) 64#usize) × Std.Usize)
  := do
  loop
    (fun (rows1, bit1) => decode.affine.frobenius_columns_loop1_loop0.body
      power rows1 bit1)
    (rows, bit)

/-- [bulksketch::decode::affine::frobenius_columns]: loop body 1:
    Source: 'src/decode/affine.rs', lines 361:4-368:5 -/
@[rust_loop_body]
def decode.affine.frobenius_columns_loop1.body
  (rows : Array (Array Std.U64 64#usize) 64#usize) (bit : Std.Usize)
  (power : Std.Usize) :
  Result (ControlFlow ((Array (Array Std.U64 64#usize) 64#usize) × Std.Usize
    × Std.Usize) (Array (Array Std.U64 64#usize) 64#usize))
  := do
  if power < 64#usize
  then
    let (rows1, bit1) ←
      decode.affine.frobenius_columns_loop1_loop0 rows 0#usize power
    let power1 ← power + 1#usize
    ok (cont (rows1, bit1, power1))
  else ok (done rows)

/-- [bulksketch::decode::affine::frobenius_columns]: loop 1:
    Source: 'src/decode/affine.rs', lines 361:4-368:5 -/
@[rust_loop]
def decode.affine.frobenius_columns_loop1
  (rows : Array (Array Std.U64 64#usize) 64#usize) (bit : Std.Usize)
  (power : Std.Usize) :
  Result (Array (Array Std.U64 64#usize) 64#usize)
  := do
  loop
    (fun (rows1, bit1, power1) => decode.affine.frobenius_columns_loop1.body
      rows1 bit1 power1)
    (rows, bit, power)

/-- [bulksketch::decode::affine::frobenius_columns]:
    Source: 'src/decode/affine.rs', lines 353:0-370:1 -/
def decode.affine.frobenius_columns
  : Result (Array (Array Std.U64 64#usize) 64#usize) := do
  let a := Array.repeat 64#usize 0#u64
  let rows := Array.repeat 64#usize a
  let (rows1, bit) ← decode.affine.frobenius_columns_loop0 rows 0#usize
  decode.affine.frobenius_columns_loop1 rows1 bit 1#usize

/-- [bulksketch::decode::affine::FROBENIUS_COLUMNS]
    Source: 'src/decode/affine.rs', lines 351:0-351:64 -/
@[global_simps, irreducible]
def decode.affine.FROBENIUS_COLUMNS
  : Result (Array (Array Std.U64 64#usize) 64#usize) :=
  decode.affine.frobenius_columns

/-- [bulksketch::decode::affine::solve_map]: loop body 1:
    Source: 'src/decode/affine.rs', lines 188:16-190:17 -/
@[rust_loop_body]
def decode.affine.solve_map_loop0_loop0.body
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    Std.U64) (core.slice.iter.Iter Std.U64)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64) →
    core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64))) ((core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) ×
    (core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64))))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      Std.U64) (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done (iter1, fun z => let z1 := next_back z none
                                      back z1))
  | some p =>
    let (dst, value) := p
    let dst1 ← lift (dst ^^^ value)
    ok (cont (iter1,
      fun z => let z1 := next_back z (some (dst1, value))
               back z1))

/-- [bulksketch::decode::affine::solve_map]: loop 1:
    Source: 'src/decode/affine.rs', lines 188:16-190:17 -/
@[rust_loop]
def decode.affine.solve_map_loop0_loop0
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) :
  Result ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64) →
    core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64)))
  := do
  loop
    (fun (iter1, back1) => decode.affine.solve_map_loop0_loop0.body iter1
      back1)
    (iter, back)

section MutableStep
local notation "core.iter.adapters.enumerate.IteratorEnumerate.next" => Aeneas.Std.MutableEnumerate.next

/-- [bulksketch::decode::affine::solve_map]: loop body 2:
    Source: 'src/decode/affine.rs', lines 195:12-197:13 -/
@[rust_loop_body]
def decode.affine.solve_map_loop0_loop1.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (power : Std.Usize) (coefficient : Std.U64)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  Std.U64))
  (back : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  Std.U64) → core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  Std.U64)) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut Std.U64)) ×
    (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut Std.U64)
    → core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
    Std.U64))) ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut Std.U64)) ×
    (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut Std.U64)
    → core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
    Std.U64))))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      Std.U64) iter
  match o with
  | none => ok (done (iter1, fun e => let e1 := next_back e none
                                      back e1))
  | some p =>
    let (bit, dst) := p
    let i ← 1#u64 <<< bit
    let i1 ← lift (UScalar.cast .U32 power)
    let i2 ← backendcontractBulkKernelsInst.ArithmeticInst.frobenius i i1
    let i3 ← backendcontractBulkKernelsInst.ArithmeticInst.mul coefficient i2
    let dst1 ← lift (dst ^^^ i3)
    ok (cont (iter1,
      fun e => let e1 := next_back e (some (bit, dst1))
               back e1))

end MutableStep

/-- [bulksketch::decode::affine::solve_map]: loop 2:
    Source: 'src/decode/affine.rs', lines 195:12-197:13 -/
@[rust_loop]
def decode.affine.solve_map_loop0_loop1
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  Std.U64))
  (back : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  Std.U64) → core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  Std.U64)) (power : Std.Usize) (coefficient : Std.U64) :
  Result ((core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
    Std.U64)) × (core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut Std.U64) →
    core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut Std.U64)))
  := do
  loop
    (fun (iter1, back1) => decode.affine.solve_map_loop0_loop1.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst power coefficient
      iter1 back1)
    (iter, back)

section MutableConstruct
local notation "core.iter.traits.iterator.Iterator.enumerate.trait_default" => Aeneas.Std.MutableEnumerate.construct

/-- [bulksketch::decode::affine::solve_map]: loop body 0:
    Source: 'src/decode/affine.rs', lines 181:4-199:5 -/
@[rust_loop_body]
def decode.affine.solve_map_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (i : Std.U32) (bits : Std.Usize)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (columns : Array Std.U64 64#usize) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.U64)) × (Array Std.U64 64#usize)) (Array Std.U64
    64#usize))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done columns)
  | some p =>
    let (power, coefficient) := p
    if coefficient = 0#u64
    then ok (cont (iter1, columns))
    else
      if i = 64#u32
      then
        let a ← decode.affine.FROBENIUS_COLUMNS
        let row ← Array.index_usize a power
        if coefficient = 1#u64
        then
          let (s, to_slice_mut_back) ← lift (Array.to_slice_mut columns)
          let (im, iter_mut_back) ← core.slice.Slice.iter_mut s
          let (iter2, trait_default_back) ←
            core.iter.traits.iterator.Iterator.zip.trait_default
              (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
              Std.U64)
              (SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
              Std.U64 64#usize) im row
          let (z, back) ←
            decode.affine.solve_map_loop0_loop0 iter2 (fun z1 => z1)
          let z1 := back z
          let im1 := trait_default_back z1
          let s1 := iter_mut_back im1
          let a1 := to_slice_mut_back s1
          ok (cont (iter1, a1))
        else
          let (s, to_slice_mut_back) ← lift (Array.to_slice_mut columns)
          let s1 ← lift (Array.to_slice row)
          let s2 ←
            backendcontractBulkKernelsInst.ArithmeticInst.scale_xor s s1
              coefficient
          let columns1 := to_slice_mut_back s2
          ok (cont (iter1, columns1))
      else
        let (s, index_mut_back) ←
          core.array.Array.index_mut (core.ops.index.IndexMutSlice
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)) columns
            { «end» := bits }
        let (im, iter_mut_back) ← core.slice.Slice.iter_mut s
        let (iter2, trait_default_back) ←
          core.iter.traits.iterator.Iterator.enumerate.trait_default
            (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
            Std.U64) im
        let (e, back) ←
          decode.affine.solve_map_loop0_loop1 fieldBinaryFieldInst
            backendcontractBulkKernelsInst iter2 (fun e1 => e1) power
            coefficient
        let e1 := back e
        let im1 := trait_default_back e1
        let s1 := iter_mut_back im1
        let a := index_mut_back s1
        ok (cont (iter1, a))

end MutableConstruct

/-- [bulksketch::decode::affine::solve_map]: loop 0:
    Source: 'src/decode/affine.rs', lines 181:4-199:5 -/
@[rust_loop]
def decode.affine.solve_map_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (i : Std.U32)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (bits : Std.Usize) (columns : Array Std.U64 64#usize) :
  Result (Array Std.U64 64#usize)
  := do
  loop
    (fun (iter1, columns1) => decode.affine.solve_map_loop0.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst i bits iter1
      columns1)
    (iter, columns)

/-- [bulksketch::decode::affine::solve_map]: loop body 4:
    Source: 'src/decode/affine.rs', lines 206:8-215:9 -/
@[rust_loop_body]
def decode.affine.solve_map_loop1_loop0.body
  (images : Array Std.U64 64#usize) (preimages : Array Std.U64 64#usize)
  (original : Std.U64) (image : Std.U64) :
  Result (ControlFlow (Std.U64 × Std.U64) ((Array Std.U64 64#usize) × (Array
    Std.U64 64#usize) × Std.U64 × Std.U64))
  := do
  if image != 0#u64
  then
    let i ← core.num.U64.trailing_zeros image
    let pivot ← lift (UScalar.cast .Usize i)
    let i1 ← Array.index_usize images pivot
    if i1 = 0#u64
    then
      let a ← Array.update images pivot image
      let a1 ← Array.update preimages pivot original
      ok (done (a, a1, original, image))
    else
      let image1 ← lift (image ^^^ i1)
      let i2 ← Array.index_usize preimages pivot
      let original1 ← lift (original ^^^ i2)
      ok (cont (original1, image1))
  else ok (done (images, preimages, original, image))

/-- [bulksketch::decode::affine::solve_map]: loop 4:
    Source: 'src/decode/affine.rs', lines 206:8-215:9 -/
@[rust_loop]
def decode.affine.solve_map_loop1_loop0
  (images : Array Std.U64 64#usize) (preimages : Array Std.U64 64#usize)
  (original : Std.U64) (image : Std.U64) :
  Result ((Array Std.U64 64#usize) × (Array Std.U64 64#usize) × Std.U64 ×
    Std.U64)
  := do
  loop
    (fun (original1, image1) => decode.affine.solve_map_loop1_loop0.body images
      preimages original1 image1)
    (original, image)

/-- [bulksketch::decode::affine::solve_map]: loop body 3:
    Source: 'src/decode/affine.rs', lines 203:4-220:5 -/
@[rust_loop_body]
def decode.affine.solve_map_loop1.body
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (kernel : Array Std.U64 64#usize) (images : Array Std.U64 64#usize)
  (preimages : Array Std.U64 64#usize) (rank : Std.Usize) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.U64)) × (Array Std.U64 64#usize) × (Array
    Std.U64 64#usize) × (Array Std.U64 64#usize) × Std.Usize) ((Array Std.U64
    64#usize) × (Array Std.U64 64#usize) × (Array Std.U64 64#usize) ×
    Std.Usize))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done (kernel, images, preimages, rank))
  | some p =>
    let (bit, column) := p
    let original ← 1#u64 <<< bit
    let (images1, preimages1, original1, image) ←
      decode.affine.solve_map_loop1_loop0 images preimages original column
    if image = 0#u64
    then
      let a ← Array.update kernel rank original1
      let rank1 ← rank + 1#usize
      ok (cont (iter1, a, images1, preimages1, rank1))
    else ok (cont (iter1, kernel, images1, preimages1, rank))

/-- [bulksketch::decode::affine::solve_map]: loop 3:
    Source: 'src/decode/affine.rs', lines 203:4-220:5 -/
@[rust_loop]
def decode.affine.solve_map_loop1
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (kernel : Array Std.U64 64#usize) (images : Array Std.U64 64#usize)
  (preimages : Array Std.U64 64#usize) (rank : Std.Usize) :
  Result ((Array Std.U64 64#usize) × (Array Std.U64 64#usize) × (Array
    Std.U64 64#usize) × Std.Usize)
  := do
  loop
    (fun (iter1, kernel1, images1, preimages1, rank1) =>
      decode.affine.solve_map_loop1.body iter1 kernel1 images1 preimages1
      rank1)
    (iter, kernel, images, preimages, rank)

/-- [bulksketch::decode::affine::solve_map]: loop body 5:
    Source: 'src/decode/affine.rs', lines 223:4-232:1 -/
@[rust_loop_body]
def decode.affine.solve_map_loop2.body
  (images : Array Std.U64 64#usize) (preimages : Array Std.U64 64#usize)
  (rank : Std.Usize) (target : Std.U64) (solution : Std.U64) :
  Result (ControlFlow (Std.U64 × Std.U64) (Option (Std.U64 × Std.Usize)))
  := do
  if target != 0#u64
  then
    let i ← core.num.U64.trailing_zeros target
    let pivot ← lift (UScalar.cast .Usize i)
    let i1 ← Array.index_usize images pivot
    if i1 = 0#u64
    then ok (done none)
    else
      let target1 ← lift (target ^^^ i1)
      let i2 ← Array.index_usize preimages pivot
      let solution1 ← lift (solution ^^^ i2)
      ok (cont (target1, solution1))
  else ok (done (some (solution, rank)))

/-- [bulksketch::decode::affine::solve_map]: loop 5:
    Source: 'src/decode/affine.rs', lines 223:4-232:1 -/
@[rust_loop]
def decode.affine.solve_map_loop2
  (images : Array Std.U64 64#usize) (preimages : Array Std.U64 64#usize)
  (rank : Std.Usize) (target : Std.U64) (solution : Std.U64) :
  Result (Option (Std.U64 × Std.Usize))
  := do
  loop
    (fun (target1, solution1) => decode.affine.solve_map_loop2.body images
      preimages rank target1 solution1)
    (target, solution)

/-- [bulksketch::decode::affine::solve_map]:
    Source: 'src/decode/affine.rs', lines 175:0-232:1 -/
def decode.affine.solve_map
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (affine : Slice Std.U64) (kernel : Array Std.U64 64#usize) :
  Result ((Option (Std.U64 × Std.Usize)) × (Array Std.U64 64#usize))
  := do
  let i ← fieldBinaryFieldInst.BITS
  let bits ← lift (UScalar.cast .Usize i)
  let columns := Array.repeat 64#usize 0#u64
  let s ←
    core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U64) affine
      { start := 1#usize }
  let i1 ← core.slice.Slice.iter s
  let iter ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter Std.U64) i1
  let columns1 ←
    decode.affine.solve_map_loop0 fieldBinaryFieldInst
      backendcontractBulkKernelsInst i iter bits columns
  let images := Array.repeat 64#usize 0#u64
  let preimages := Array.repeat 64#usize 0#u64
  let s1 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)) columns1
      { «end» := bits }
  let i2 ← core.slice.Slice.iter s1
  let iter1 ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter Std.U64) i2
  let (kernel1, images1, preimages1, rank) ←
    decode.affine.solve_map_loop1 iter1 kernel images preimages 0#usize
  let target ← Slice.index_usize affine 0#usize
  let o ← decode.affine.solve_map_loop2 images1 preimages1 rank target 0#u64
  ok (o, kernel1)

end bulksketch
