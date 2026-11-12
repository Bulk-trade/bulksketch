-- Exact original-source declaration projection. The imports reuse checked dependencies.
module
public import Arithmetic.AffineQuarticGenerated
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

/-- [bulksketch::decode::deg34::quartic]: loop body 0:
    Source: 'src/decode/deg34.rs', lines 185:4-187:5 -/
@[rust_loop_body]
def decode.deg34.quartic_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (roots : Array Std.U64 4#usize) (iter : core.ops.range.Range Std.Usize)
  (prefixes : Array Std.U64 4#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U64
    4#usize)) (Array Std.U64 4#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done prefixes)
  | some i =>
    let i1 ← i - 1#usize
    let i2 ← Array.index_usize prefixes i1
    let i3 ← Array.index_usize roots i1
    let i4 ← backendcontractBulkKernelsInst.ArithmeticInst.mul i2 i3
    let a ← Array.update prefixes i i4
    ok (cont (iter1, a))

/-- [bulksketch::decode::deg34::quartic]: loop 0:
    Source: 'src/decode/deg34.rs', lines 185:4-187:5 -/
@[rust_loop]
def decode.deg34.quartic_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.ops.range.Range Std.Usize) (roots : Array Std.U64 4#usize)
  (prefixes : Array Std.U64 4#usize) :
  Result (Array Std.U64 4#usize)
  := do
  loop
    (fun (iter1, prefixes1) => decode.deg34.quartic_loop0.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst roots iter1
      prefixes1)
    (iter, prefixes)

/-- [bulksketch::decode::deg34::quartic]: loop body 1:
    Source: 'src/decode/deg34.rs', lines 189:4-193:5 -/
@[rust_loop_body]
def decode.deg34.quartic_loop1.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (shift : Std.U64) (prefixes : Array Std.U64 4#usize)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (roots : Array Std.U64 4#usize) (inverse : Std.U64) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range
    Std.Usize)) × (Array Std.U64 4#usize) × Std.U64) (Array Std.U64 4#usize))
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none => ok (done roots)
  | some i =>
    let original ← Array.index_usize roots i
    let i1 ← Array.index_usize prefixes i
    let i2 ← backendcontractBulkKernelsInst.ArithmeticInst.mul i1 inverse
    let i3 ← lift (i2 ^^^ shift)
    let a ← Array.update roots i i3
    let inverse1 ←
      backendcontractBulkKernelsInst.ArithmeticInst.mul inverse original
    ok (cont (iter1, a, inverse1))

/-- [bulksketch::decode::deg34::quartic]: loop 1:
    Source: 'src/decode/deg34.rs', lines 189:4-193:5 -/
@[rust_loop]
def decode.deg34.quartic_loop1
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (shift : Std.U64) (roots : Array Std.U64 4#usize)
  (prefixes : Array Std.U64 4#usize) (inverse : Std.U64) :
  Result (Array Std.U64 4#usize)
  := do
  loop
    (fun (iter1, roots1, inverse1) => decode.deg34.quartic_loop1.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst shift prefixes iter1
      roots1 inverse1)
    (iter, roots, inverse)

/-- [bulksketch::decode::deg34::quartic]:
    Source: 'src/decode/deg34.rs', lines 162:0-195:1 -/
def decode.deg34.quartic
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (factor : Slice Std.U64) :
  Result (Option (Array Std.U64 4#usize))
  := do
  let a ← Slice.index_usize factor 3#usize
  let b ← Slice.index_usize factor 2#usize
  let c ← Slice.index_usize factor 1#usize
  let d ← Slice.index_usize factor 0#usize
  if a = 0#u64
  then
    decode.deg34.affine_quartic fieldBinaryFieldInst
      backendcontractBulkKernelsInst b c d
  else
    let o ← backendcontractBulkKernelsInst.ArithmeticInst.inverse a
    let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let ratio ← backendcontractBulkKernelsInst.ArithmeticInst.mul c val
      let i ←
        backendcontractBulkKernelsInst.ArithmeticInst.frobenius ratio 31#u32
      let i1 ←
        backendcontractBulkKernelsInst.ArithmeticInst.frobenius i 31#u32
      let shift ← backendcontractBulkKernelsInst.ArithmeticInst.square i1
      let e2 ← backendcontractBulkKernelsInst.ArithmeticInst.square shift
      let i2 ← backendcontractBulkKernelsInst.ArithmeticInst.square e2
      let i3 ← backendcontractBulkKernelsInst.ArithmeticInst.mul b e2
      let i4 ← lift (i2 ^^^ i3)
      let denominator ← lift (i4 ^^^ d)
      if denominator = 0#u64
      then ok none
      else
        let o1 ←
          backendcontractBulkKernelsInst.ArithmeticInst.inverse denominator
        let cf1 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          let i5 ← backendcontractBulkKernelsInst.ArithmeticInst.mul a shift
          let i6 ← lift (b ^^^ i5)
          let i7 ← backendcontractBulkKernelsInst.ArithmeticInst.mul i6 val1
          let i8 ← backendcontractBulkKernelsInst.ArithmeticInst.mul a val1
          let o2 ←
            decode.deg34.affine_quartic fieldBinaryFieldInst
              backendcontractBulkKernelsInst i7 i8 val1
          let cf2 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o2
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let s ← lift (Array.to_slice val2)
            let b1 ← core.slice.Slice.contains core.cmp.PartialEqU64 s 0#u64
            if b1
            then ok none
            else
              let prefixes := Array.repeat 4#usize 1#u64
              let prefixes1 ←
                decode.deg34.quartic_loop0 fieldBinaryFieldInst
                  backendcontractBulkKernelsInst
                  { start := 1#usize, «end» := 4#usize } val2 prefixes
              let i9 ← Array.index_usize prefixes1 3#usize
              let i10 ← Array.index_usize val2 3#usize
              let i11 ←
                backendcontractBulkKernelsInst.ArithmeticInst.mul i9 i10
              let o3 ←
                backendcontractBulkKernelsInst.ArithmeticInst.inverse i11
              let cf3 ←
                core.option.Option.Insts.CoreOpsTry_traitTry.branch o3
              match cf3 with
              | core.ops.control_flow.ControlFlow.Continue val3 =>
                let iter ←
                  core.iter.traits.iterator.Iterator.rev.trait_default
                    (core.iter.traits.iterator.IteratorRange
                    core.iter.range.StepUsize)
                    (core.ops.range.Range.Insts.DoubleEndedIterator
                    core.iter.range.StepUsize)
                    { start := 0#usize, «end» := 4#usize }
                let roots ←
                  decode.deg34.quartic_loop1 fieldBinaryFieldInst
                    backendcontractBulkKernelsInst iter shift val2 prefixes1
                    val3
                ok (some roots)
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

/-- [bulksketch::decode::deg34::solve]:
    Source: 'src/decode/deg34.rs', lines 198:0-215:1 -/
def decode.deg34.solve
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (factor : Slice Std.U64) (output : Slice Std.U64) :
  Result ((Option Std.Usize) × (Slice Std.U64))
  := do
  let i ← fieldBinaryFieldInst.BITS
  massert (i = 64#u32)
  let i1 := Slice.len factor
  let degree ← i1 - 1#usize
  if degree = 3#usize
  then
    let i2 ← Slice.index_usize factor 2#usize
    let i3 ← Slice.index_usize factor 1#usize
    let i4 ← Slice.index_usize factor 0#usize
    let o ←
      decode.deg34.cubic fieldBinaryFieldInst backendcontractBulkKernelsInst i2
        i3 i4
    let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i5 ← Array.index_usize val 0#usize
      let i6 ← Array.index_usize val 1#usize
      let i7 ← Array.index_usize val 2#usize
      let (s, index_mut_back) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) output
          { «end» := degree }
      let s1 ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64))
          (Array.make 4#usize [ i5, i6, i7, 0#u64 ]) { «end» := degree }
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU64 s s1
      let output1 := index_mut_back s2
      ok (some degree, output1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let o1 ←
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
          Std.Usize residual
      ok (o1, output)
  else
    let o ←
      decode.deg34.quartic fieldBinaryFieldInst backendcontractBulkKernelsInst
        factor
    let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (s, index_mut_back) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) output
          { «end» := degree }
      let s1 ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)) val
          { «end» := degree }
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU64 s s1
      let output1 := index_mut_back s2
      ok (some degree, output1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let o1 ←
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
          Std.Usize residual
      ok (o1, output)

end bulksketch
