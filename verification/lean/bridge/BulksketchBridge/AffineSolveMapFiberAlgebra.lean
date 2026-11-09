import BulksketchBridge.AffineSubspaceAlgebra

namespace BulksketchBridge.AffineSubspaceAlgebra

variable {F : Type} [Field F] [CharP F 2]

theorem span_add_closed (basis : List F) {left right : F}
    (leftIn : left ∈ spanWords basis) (rightIn : right ∈ spanWords basis) :
    left + right ∈ spanWords basis := by
  induction basis generalizing left right with
  | nil =>
    simp only [spanWords, Set.mem_singleton_iff] at leftIn rightIn ⊢
    rw [leftIn, rightIn, add_zero]
  | cons direction earlier ih =>
    simp only [spanWords, Set.mem_union, Set.mem_image] at leftIn rightIn ⊢
    rcases leftIn with oldLeft | ⟨priorLeft, oldLeft, rfl⟩
    · rcases rightIn with oldRight | ⟨priorRight, oldRight, rfl⟩
      · exact Or.inl (ih oldLeft oldRight)
      · exact Or.inr ⟨left + priorRight, ih oldLeft oldRight, add_assoc ..⟩
    · rcases rightIn with oldRight | ⟨priorRight, oldRight, rfl⟩
      · exact Or.inr ⟨priorLeft + right, ih oldLeft oldRight, by ac_rfl⟩
      · have sum : (priorLeft + direction) + (priorRight + direction) = priorLeft + priorRight := by
          calc
            _ = priorLeft + priorRight + (direction + direction) := by ac_rfl
            _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]
        exact Or.inl (sum.symm ▸ ih oldLeft oldRight)

private theorem add_equal_of_sum_zero {left right : F} (zero : left + right = 0) : left = right := by
  calc
    left = (left + right) + right := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = right := by rw [zero, zero_add]

def KernelBasis (map : F → F) (inputs kernel : List F) : Prop :=
  ∀ point, point ∈ spanWords kernel ↔ point ∈ spanWords inputs ∧ map point = 0

/-- An independent image column creates a new pivot and leaves the
restricted kernel unchanged. -/
theorem extend_independent_image (map : F → F) (additive : ∀ x y, map (x + y) = map x + map y)
    (inputs kernel : List F) (direction : F) (prior : KernelBasis map inputs kernel)
    (independent : map direction ∉ map '' spanWords inputs) :
    KernelBasis map (direction :: inputs) kernel := by
  intro point
  rw [prior]
  simp only [spanWords, Set.mem_union, Set.mem_image]
  constructor
  · rintro ⟨member, root⟩
    exact ⟨Or.inl member, root⟩
  · rintro ⟨old | ⟨earlier, old, rfl⟩, root⟩
    · exact ⟨old, root⟩
    · rw [additive] at root
      exact (independent ⟨earlier, old, add_equal_of_sum_zero root⟩).elim

/-- A dependent image column records the new input bit plus its previous
preimage. That vector spans the additional part of the restricted kernel. -/
theorem extend_dependent_image (map : F → F) (additive : ∀ x y, map (x + y) = map x + map y)
    (inputs kernel : List F) (direction preimage : F) (prior : KernelBasis map inputs kernel)
    (oldPreimage : preimage ∈ spanWords inputs) (sameImage : map direction = map preimage) :
    KernelBasis map (direction :: inputs) ((direction + preimage) :: kernel) := by
  intro point
  simp only [spanWords, Set.mem_union, Set.mem_image]
  constructor
  · rintro (old | ⟨earlier, old, rfl⟩)
    · obtain ⟨member, root⟩ := (prior _).mp old
      exact ⟨Or.inl member, root⟩
    · obtain ⟨member, root⟩ := (prior _).mp old
      have merged : earlier + (direction + preimage) = (earlier + preimage) + direction := by ac_rfl
      refine ⟨Or.inr ⟨earlier + preimage, span_add_closed inputs member oldPreimage, merged.symm⟩, ?_⟩
      rw [additive, root, additive, sameImage, CharTwo.add_self_eq_zero, zero_add]
  · rintro ⟨old | ⟨earlier, old, rfl⟩, root⟩
    · exact Or.inl ((prior _).mpr ⟨old, root⟩)
    · rw [additive, sameImage] at root
      have cancel : (earlier + preimage) + (direction + preimage) = earlier + direction := by
        calc
          _ = earlier + direction + (preimage + preimage) := by ac_rfl
          _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]
      refine Or.inr ⟨earlier + preimage, (prior _).mpr ⟨span_add_closed inputs old oldPreimage, ?_⟩, cancel⟩
      rwa [additive]

theorem dependent_direction_independent (map : F → F) (inputs kernel : List F) (direction preimage : F)
    (prior : KernelBasis map inputs kernel) (oldPreimage : preimage ∈ spanWords inputs)
    (newInput : direction ∉ spanWords inputs) :
    direction + preimage ∉ spanWords kernel := by
  intro member
  have old := (prior _).mp member
  have added := span_add_closed inputs old.1 oldPreimage
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero] at added
  exact newInput added

/-- A recovered particular preimage and a complete kernel basis determine
    the whole affine fiber used by the original enumerator. -/
theorem fiber_of_kernel_basis (map : F → F) (additive : ∀ x y, map (x + y) = map x + map y)
    (basis : List F) (base target point : F)
    (kernel : ∀ x, map x = 0 ↔ x ∈ spanWords basis) (solved : map base = target) :
    map point = target ↔ point ∈ coset base basis := by
  change map point = target ↔ point + base ∈ spanWords basis
  rw [← kernel, additive, solved]
  constructor
  · intro equal
    rw [equal, CharTwo.add_self_eq_zero]
  · exact add_equal_of_sum_zero

#print axioms extend_independent_image
#print axioms extend_dependent_image
#print axioms fiber_of_kernel_basis

end BulksketchBridge.AffineSubspaceAlgebra
