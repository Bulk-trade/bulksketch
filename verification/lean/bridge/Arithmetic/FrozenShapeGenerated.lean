-- Original checked FrozenSketch shape accessor.
import Arithmetic.RowLocalGenerated

open Aeneas Aeneas.Std Result Error
set_option linter.unusedVariables false

namespace BulksketchBridge.FrozenShapeRuntime

/-- Read the immutable payload under the shared Arc value abstraction. -/
def arcDeref {T : Type} (_allocator : Type) (value : T) : Result T := .ok value

end BulksketchBridge.FrozenShapeRuntime

namespace bulksketch

local notation "alloc.alloc.Global" => Unit
local notation "alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref" =>
  BulksketchBridge.FrozenShapeRuntime.arcDeref

/-- [bulksketch::sketch::state::{bulksketch::sketch::state::FrozenSketch<F>}::shape]:
    Source: 'src/sketch/state.rs', lines 233:4-235:5
    Visibility: public -/
def sketch.state.FrozenSketch.shape
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (self : sketch.state.FrozenSketch F) :
  Result (sketch.shape.SketchShape F)
  := do
  let s ←
    alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref alloc.alloc.Global self.state
  alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref alloc.alloc.Global s.shape

end bulksketch
