-- Exact original AVX square kernel. The masked memory operations are explicit slots.
import Arithmetic.AvxSquareRuntime

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxRecDepth 4096

namespace bulksketch

variable (loadModel : Aeneas.Std.AvxSquareRuntime.Load)
variable (storeModel : Aeneas.Std.AvxSquareRuntime.Store)

local notation "core.core_arch.x86.__m512i" => Avx512Register.Word512
local notation "core.core_arch.x86.avx512f._mm512_setzero_si512" => AvxSquareRuntime.zero
local notation "core.core_arch.x86.avx512f._mm512_set1_epi64" => Avx512Register.broadcast
local notation "core.core_arch.x86.avx512f._mm512_unpacklo_epi64" => Avx512Register.unpack false
local notation "core.core_arch.x86.avx512f._mm512_unpackhi_epi64" => Avx512Register.unpack true
local notation "core.core_arch.x86.avx512f._mm512_xor_si512" => Avx512Register.xorWords
local notation "core.num.Usize.div_ceil" => DenseReducerSquareRuntime.divCeil
local notation "core.num.U64.to_ne_bytes" => X86PclmulRuntime.unsignedBytes
local notation "core.num.I64.from_ne_bytes" => X86PclmulRuntime.signedFromBytes
local notation "core.iter.adapters.skip.Skip" => AvxSquareRuntime.Skip
local notation "core.iter.traits.iterator.Iterator.skip.default" => AvxSquareRuntime.skip
local notation "core.iter.adapters.skip.Skip.Insts.CoreIterTraitsIteratorIterator.next" => AvxSquareRuntime.skipNext
local notation "backend.x86_vpclmul512.load" => loadModel
local notation "backend.x86_vpclmul512.store" => storeModel

/-- [bulksketch::backend::x86_vpclmul512::square_mod]: loop body 0:
    Source: 'src/backend/x86_vpclmul512.rs', lines 222:4-228:5 -/
@[rust_loop_body]
def backend.x86_vpclmul512.square_mod_loop0.body
  (first_high : Std.Usize)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (dst : Slice Std.U64) (scratch : Slice types.RawProduct) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.U64)) × (Slice Std.U64) × (Slice
    types.RawProduct)) ((Slice Std.U64) × (Slice types.RawProduct)))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done (dst, scratch))
  | some p =>
    let (i, coefficient) := p
    let square ←
      backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.square
        field.Gf64.Insts.BulksketchFieldBinaryField coefficient
    let (rp, index_mut_back) ← Slice.index_mut_usize scratch i
    if i < first_high
    then
      let i1 ← 2#usize * i
      let s ← Slice.update dst i1 square
      let s1 := index_mut_back { rp with lo := square }
      ok (cont (iter1, s, s1))
    else
      let s := index_mut_back { rp with lo := square }
      ok (cont (iter1, dst, s))

/-- [bulksketch::backend::x86_vpclmul512::square_mod]: loop 0:
    Source: 'src/backend/x86_vpclmul512.rs', lines 222:4-228:5 -/
@[rust_loop]
def backend.x86_vpclmul512.square_mod_loop0
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (dst : Slice Std.U64) (scratch : Slice types.RawProduct)
  (first_high : Std.Usize) :
  Result ((Slice Std.U64) × (Slice types.RawProduct))
  := do
  loop
    (fun (iter1, dst1, scratch1) =>
      backend.x86_vpclmul512.square_mod_loop0.body first_high iter1 dst1
      scratch1)
    (iter, dst, scratch)

/-- [bulksketch::backend::x86_vpclmul512::square_mod]: loop body 2:
    Source: 'src/backend/x86_vpclmul512.rs', lines 236:8-242:9 -/
@[rust_loop_body]
def backend.x86_vpclmul512.square_mod_loop1_loop0.body
  (table : Slice Std.U64) (degree : Std.Usize) (first_high : Std.Usize)
  (offset : Std.Usize) («end» : Std.Usize)
  (iter : core.iter.adapters.skip.Skip (core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.Iter types.RawProduct))) (even : core.core_arch.x86.__m512i)
  (odd : core.core_arch.x86.__m512i) :
  Result (ControlFlow ((core.iter.adapters.skip.Skip
    (core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
    types.RawProduct))) × core.core_arch.x86.__m512i ×
    core.core_arch.x86.__m512i) (core.core_arch.x86.__m512i ×
    core.core_arch.x86.__m512i))
  := do
  let (o, iter1) ←
    core.iter.adapters.skip.Skip.Insts.CoreIterTraitsIteratorIterator.next
      (core.iter.traits.iterator.IteratorEnumerate
      (core.iter.traits.iterator.IteratorSliceIter types.RawProduct)) iter
  match o with
  | none => ok (done (even, odd))
  | some p =>
    let (i, square) := p
    let i1 ← i - first_high
    let start ← i1 * degree
    let a ← core.num.U64.to_ne_bytes square.lo
    let i2 ← core.num.I64.from_ne_bytes a
    let scale ← core.core_arch.x86.avx512f._mm512_set1_epi64 i2
    let i3 ← start + offset
    let i4 ← start + «end»
    let s ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U64) table { start := i3, «end» := i4 }
    let mi ← backend.x86_vpclmul512.load s
    let (lo, hi) ← backend.x86_vpclmul512.raw scale mi
    let even1 ← core.core_arch.x86.avx512f._mm512_xor_si512 even lo
    let odd1 ← core.core_arch.x86.avx512f._mm512_xor_si512 odd hi
    ok (cont (iter1, even1, odd1))

local notation "backend.x86_vpclmul512.square_mod_loop1_loop0.body" =>
  (backend.x86_vpclmul512.square_mod_loop1_loop0.body loadModel)

/-- [bulksketch::backend::x86_vpclmul512::square_mod]: loop 2:
    Source: 'src/backend/x86_vpclmul512.rs', lines 236:8-242:9 -/
@[rust_loop]
def backend.x86_vpclmul512.square_mod_loop1_loop0
  (iter : core.iter.adapters.skip.Skip (core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.Iter types.RawProduct))) (table : Slice Std.U64)
  (degree : Std.Usize) (first_high : Std.Usize) (offset : Std.Usize)
  («end» : Std.Usize) (even : core.core_arch.x86.__m512i)
  (odd : core.core_arch.x86.__m512i) :
  Result (core.core_arch.x86.__m512i × core.core_arch.x86.__m512i)
  := do
  loop
    (fun (iter1, even1, odd1) =>
      backend.x86_vpclmul512.square_mod_loop1_loop0.body table degree
      first_high offset «end» iter1 even1 odd1)
    (iter, even, odd)

local notation "backend.x86_vpclmul512.square_mod_loop1_loop0" =>
  (backend.x86_vpclmul512.square_mod_loop1_loop0 loadModel)

/-- [bulksketch::backend::x86_vpclmul512::square_mod]: loop body 1:
    Source: 'src/backend/x86_vpclmul512.rs', lines 232:4-249:5 -/
@[rust_loop_body]
def backend.x86_vpclmul512.square_mod_loop1.body
  (a : Slice Std.U64) (table : Slice Std.U64)
  (scratch : Slice types.RawProduct) (degree : Std.Usize)
  (first_high : Std.Usize)
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (dst : Slice Std.U64) :
  Result (ControlFlow ((core.iter.adapters.step_by.StepBy (core.ops.range.Range
    Std.Usize)) × (Slice Std.U64)) (Slice Std.U64))
  := do
  let (o, iter1) ←
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
  match o with
  | none => ok (done dst)
  | some offset =>
    let i ← offset + 8#usize
    let «end» ← lift (core.cmp.impls.OrdUsize.min i degree)
    let even ← core.core_arch.x86.avx512f._mm512_setzero_si512
    let i1 := Slice.len a
    let s ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice types.RawProduct) scratch
        { «end» := i1 }
    let i2 ← core.slice.Slice.iter s
    let e ←
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter types.RawProduct) i2
    let iter2 ←
      core.iter.traits.iterator.Iterator.skip.default
        (core.iter.traits.iterator.IteratorEnumerate
        (core.iter.traits.iterator.IteratorSliceIter types.RawProduct)) e
        first_high
    let (even1, odd) ←
      backend.x86_vpclmul512.square_mod_loop1_loop0 iter2 table degree
        first_high offset «end» even even
    let mi ← core.core_arch.x86.avx512f._mm512_unpacklo_epi64 even1 odd
    let mi1 ← core.core_arch.x86.avx512f._mm512_unpackhi_epi64 even1 odd
    let result ← backend.x86_vpclmul512.reduce_shift mi mi1
    let (out, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) dst
        { start := offset, «end» }
    let mi2 ← backend.x86_vpclmul512.load out
    let mi3 ← core.core_arch.x86.avx512f._mm512_xor_si512 mi2 result
    let out1 ← backend.x86_vpclmul512.store out mi3
    let dst1 := index_mut_back out1
    ok (cont (iter1, dst1))

local notation "backend.x86_vpclmul512.square_mod_loop1.body" =>
  (backend.x86_vpclmul512.square_mod_loop1.body loadModel storeModel)

/-- [bulksketch::backend::x86_vpclmul512::square_mod]: loop 1:
    Source: 'src/backend/x86_vpclmul512.rs', lines 232:4-249:5 -/
@[rust_loop]
def backend.x86_vpclmul512.square_mod_loop1
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (a : Slice Std.U64) (table : Slice Std.U64) (dst : Slice Std.U64)
  (scratch : Slice types.RawProduct) (degree : Std.Usize)
  (first_high : Std.Usize) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (iter1, dst1) => backend.x86_vpclmul512.square_mod_loop1.body a table
      scratch degree first_high iter1 dst1)
    (iter, dst)

local notation "backend.x86_vpclmul512.square_mod_loop1" =>
  (backend.x86_vpclmul512.square_mod_loop1 loadModel storeModel)

/-- [bulksketch::backend::x86_vpclmul512::square_mod]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 218:0-250:1 -/
def backend.x86_vpclmul512.square_mod
  (a : Slice Std.U64) (table : Slice Std.U64) (dst : Slice Std.U64)
  (scratch : Slice types.RawProduct) :
  Result ((Slice Std.U64) × (Slice types.RawProduct))
  := do
  let degree := Slice.len dst
  let first_high ← core.num.Usize.div_ceil degree 2#usize
  let dst1 ← core.slice.Slice.fill core.clone.CloneU64 dst 0#u64
  let i ← core.slice.Slice.iter a
  let iter ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter Std.U64) i
  let (dst2, scratch1) ←
    backend.x86_vpclmul512.square_mod_loop0 iter dst1 scratch first_high
  let iter1 ←
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» := degree } 8#usize
  let dst3 ←
    backend.x86_vpclmul512.square_mod_loop1 iter1 a table dst2 scratch1 degree
      first_high
  ok (dst3, scratch1)

end bulksketch
