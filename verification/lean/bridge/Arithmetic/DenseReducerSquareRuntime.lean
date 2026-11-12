-- Exact usize ceiling division used by the source modular square.
import Arithmetic.DenseReducerTableRuntime

open Aeneas Aeneas.Std Result

namespace bulksketch

def DenseReducerSquareRuntime.divCeil (numerator denominator : Usize) : Result Usize := do
  let quotient ← numerator / denominator
  let remainder ← numerator % denominator
  if remainder > 0#usize then quotient + 1#usize else .ok quotient

end bulksketch
