import Arithmetic.FrozenShapeGenerated

namespace BulksketchBridge.FrozenShape

open Aeneas Aeneas.Std Result Error
open bulksketch.sketch.state

abbrev Field := bulksketch.field.BinaryField

def ActualFrozenShape : Prop :=
  ∀ {F : Type} (field : Field F) (self : FrozenSketch F),
    FrozenSketch.shape field self = .ok self.state.shape

theorem frozen_shape_refines : ActualFrozenShape := by
  intro F field self
  simp only [FrozenSketch.shape, FrozenShapeRuntime.arcDeref, bind_ok]

#print axioms frozen_shape_refines

end BulksketchBridge.FrozenShape
