-- Exact original candidate row-slice declaration from stock checked extraction.
import Arithmetic.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace bulksketch

/-- [bulksketch::sketch::candidates::row]:
    Source: 'src/sketch/candidates.rs', lines 65:0-73:1 -/
def sketch.candidates.row
  (storage : Slice Std.U64) (raw_count : Std.Usize) (bucket : Std.Usize) :
  Result (Slice Std.U64)
  := do
  if raw_count = 0#usize
  then
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice
      Std.U64) storage { «end» := 0#usize }
  else
    let i ← 2#usize * raw_count
    let offsets ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U64) storage
        { start := i }
    let i1 ← Slice.index_usize offsets bucket
    let r ← Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from i1
    let start ←
      core.result.Result.expect
        core.num.error.TryFromIntError.Insts.CoreFmtDebug r (toStr
        "admitted candidate offset")
    let i2 ← bucket + 1#usize
    let i3 ← Slice.index_usize offsets i2
    let r1 ← Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from i3
    let «end» ←
      core.result.Result.expect
        core.num.error.TryFromIntError.Insts.CoreFmtDebug r1 (toStr
        "admitted candidate offset")
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U64) storage { start, «end» }

end bulksketch
