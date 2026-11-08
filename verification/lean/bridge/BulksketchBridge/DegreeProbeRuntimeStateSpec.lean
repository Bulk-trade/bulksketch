import Arithmetic.DegreeProbeGenerated

namespace BulksketchBridge.DegreeProbeRuntime

open Aeneas.Std bulksketch.decode.degree_probe bulksketch.decode.row

/-- The first probe state and the exact two admission bounds. -/
def initialState : DegreeProbe :=
  { degree := 3#u8, count := 0#u8, next := some .GuardThree }

def expectedNew (budget : RowBudget) (capacity : Usize) : Option DegreeProbe :=
  if 3 ≤ budget.nonzero.val ∧ 3 ≤ capacity.val then some initialState else none

/-- Reject a degree-three probe into degree four only when both bounds allow it. -/
def expectedReject (self : DegreeProbe) (capacity : Usize) (budget : RowBudget) : DegreeProbe :=
  if self.degree.val = 3 ∧ 4 ≤ capacity.val ∧ 4 ≤ budget.nonzero.val then
    { degree := 4#u8, count := 0#u8, next := some .GuardFour }
  else
    { self with count := 0#u8, next := some .Reconstruction }

def ActualDegreeProbeNew : Prop :=
  ∀ (budget : RowBudget) (capacity : Usize),
    DegreeProbe.new budget capacity = .ok (expectedNew budget capacity)

def ActualDegreeProbeNextStage : Prop :=
  ∀ self : DegreeProbe, DegreeProbe.next_stage self = .ok self.next

def ActualDegreeProbeCount : Prop :=
  ∀ self : DegreeProbe, ∃ count : Usize,
    DegreeProbe.impl.count self = .ok count ∧ count.val = self.count.val

def ActualDegreeProbeReject : Prop :=
  ∀ (self : DegreeProbe) (capacity : Usize) (budget : RowBudget),
    DegreeProbe.reject self capacity budget = .ok (expectedReject self capacity budget)

end BulksketchBridge.DegreeProbeRuntime
