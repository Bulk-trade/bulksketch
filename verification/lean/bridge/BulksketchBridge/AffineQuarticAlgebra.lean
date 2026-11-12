import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace BulksketchBridge.AffineQuartic

variable {K : Type} [Field K] [CharP K 2]

def quadratic (u z : K) : K := z ^ 2 + u * z

def quartic (u v d z : K) : K :=
  z ^ 4 + (v + u ^ 2) * z ^ 2 + (u * v) * z + d

theorem quartic_composition (u v d z : K) :
    quartic u v d z = quadratic v (quadratic u z) + d := by
  unfold quartic quadratic
  rw [CharTwo.add_sq]
  ring

theorem translate_quadratic (u z : K) : quadratic u (z + u) = quadratic u z := by
  unfold quadratic
  rw [CharTwo.add_sq, mul_add]
  calc
    z ^ 2 + u ^ 2 + (u * z + u * u) = (z ^ 2 + u * z) + (u ^ 2 + u ^ 2) := by ring
    _ = z ^ 2 + u * z := by rw [CharTwo.add_self_eq_zero, add_zero]

omit [CharP K 2] in
private theorem unequal_translate (u z : K) (nonzero : u ≠ 0) : z ≠ z + u := by
  intro equal
  have canceled : (0 : K) = u := add_left_cancel (by simpa using equal : z + 0 = z + u)
  exact nonzero canceled.symm

/-- Algebraic step used by the native affine quartic branch after the three
normalized quadratic solves. The two different quadratic fibers each give
a translated pair of roots. -/
theorem affine_four_roots (u v d w x y : K) (nonzeroU : u ≠ 0) (nonzeroV : v ≠ 0)
    (wRoot : quadratic v w = d)
    (xRoot : quadratic u x = w) (yRoot : quadratic u y = w + v) :
    (∀ z ∈ [x, x + u, y, y + u], quartic u v d z = 0) ∧
      ([x, x + u, y, y + u] : List K).Nodup := by
  have differentFibers : w ≠ w + v := unequal_translate v w nonzeroV
  have disjoint (a b : K) (ha : quadratic u a = w) (hb : quadratic u b = w + v) :
      a ≠ b := by
    intro equal
    exact differentFibers (ha.symm.trans ((congrArg (quadratic u) equal).trans hb))
  have xTranslated : quadratic u (x + u) = w := (translate_quadratic u x).trans xRoot
  have yTranslated : quadratic u (y + u) = w + v := (translate_quadratic u y).trans yRoot
  have rootAt (z : K) (fiber : quadratic u z = w ∨ quadratic u z = w + v) :
      quartic u v d z = 0 := by
    rw [quartic_composition]
    rcases fiber with first | second
    · rw [first, wRoot, CharTwo.add_self_eq_zero]
    · rw [second, translate_quadratic, wRoot, CharTwo.add_self_eq_zero]
  constructor
  · intro z member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact rootAt _ (Or.inl xRoot)
    · exact rootAt _ (Or.inl xTranslated)
    · exact rootAt _ (Or.inr yRoot)
    · exact rootAt _ (Or.inr yTranslated)
  · simp [List.nodup_cons, unequal_translate u x nonzeroU, unequal_translate u y nonzeroU,
      disjoint x y xRoot yRoot, disjoint x (y + u) xRoot yTranslated,
      disjoint (x + u) y xTranslated yRoot, disjoint (x + u) (y + u) xTranslated yTranslated]

theorem quadratic_add (u x y : K) :
    quadratic u (x + y) = quadratic u x + quadratic u y := by
  unfold quadratic
  rw [CharTwo.add_sq, mul_add]
  ring

theorem quadratic_zero_cases (u z : K) (zero : quadratic u z = 0) :
    z = 0 ∨ z = u := by
  have product : z * (z + u) = 0 := by
    calc
      z * (z + u) = quadratic u z := by unfold quadratic; ring
      _ = 0 := zero
  rcases mul_eq_zero.mp product with h | h
  · exact Or.inl h
  · right
    calc
      z = (z + u) + u := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = u := by rw [h, zero_add]

theorem quadratic_fiber (u z w : K) (equal : quadratic u z = quadratic u w) :
    z = w ∨ z = w + u := by
  have vanishes : quadratic u (z + w) = 0 := by
    rw [quadratic_add, equal, CharTwo.add_self_eq_zero]
  rcases quadratic_zero_cases u (z + w) vanishes with same | translated
  · left
    calc
      z = (z + w) + w := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = w := by rw [same, zero_add]
  · right
    calc
      z = (z + w) + w := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = w + u := by rw [translated, add_comm]

theorem factor_from_kernel_root (b c u : K) (root : u ^ 3 + b * u + c = 0) :
    u * (b + u ^ 2) = c := by
  calc
    u * (b + u ^ 2) = (u ^ 3 + b * u + c) + c := by
      calc
        _ = (u ^ 3 + b * u) + (c + c) := by rw [CharTwo.add_self_eq_zero, add_zero]; ring
        _ = _ := by ring
    _ = c := by rw [root, zero_add]

theorem nontrivial_kernel_fiber (u v r : K)
    (root : r ^ 3 + (v + u ^ 2) * r + u * v = 0) (nonzero : r ≠ 0) (other : r ≠ u) :
    quadratic u r = v := by
  have vanishes : quadratic v (quadratic u r) = 0 := by
    rw [← add_zero (quadratic v (quadratic u r)), ← quartic_composition u v 0 r]
    calc
      _ = r * (r ^ 3 + (v + u ^ 2) * r + u * v) := by unfold quartic; ring
      _ = 0 := by rw [root, mul_zero]
  rcases quadratic_zero_cases v (quadratic u r) vanishes with same | shifted
  · exact ((quadratic_zero_cases u r same).elim nonzero other).elim
  · exact shifted

theorem solve_both_fibers (u v d w : K)
    (kernel : ∃ r, quadratic u r = v)
    (root : ∃ z, quartic u v d z = 0) (wRoot : quadratic v w = d) :
    (∃ x, quadratic u x = w) ∧ (∃ y, quadratic u y = w + v) := by
  obtain ⟨r, rRoot⟩ := kernel
  obtain ⟨z, zRoot⟩ := root
  have same : quadratic v (quadratic u z) = quadratic v w := by
    rw [quartic_composition] at zRoot
    rw [wRoot]
    have sum : quadratic v (quadratic u z) + d = d + d := by
      rw [zRoot, CharTwo.add_self_eq_zero]
    exact add_right_cancel sum
  rcases quadratic_fiber v (quadratic u z) w same with first | second
  · exact ⟨⟨z, first⟩, ⟨z + r, by rw [quadratic_add, first, rRoot]⟩⟩
  · exact ⟨⟨z + r, by rw [quadratic_add, second, rRoot, add_assoc,
        CharTwo.add_self_eq_zero, add_zero]⟩, ⟨z, second⟩⟩

omit [CharP K 2] in
theorem scaled_quadratic (a t z : K) (nonzero : a ≠ 0)
    (equation : z ^ 2 + z = t * a⁻¹ ^ 2) : quadratic a (a * z) = t := by
  calc
    quadratic a (a * z) = a ^ 2 * (z ^ 2 + z) := by unfold quadratic; ring
    _ = t := by rw [equation]; field_simp

omit [CharP K 2] in
theorem normalized_exists (a t : K) (nonzero : a ≠ 0)
    (root : ∃ x, quadratic a x = t) : ∃ z, z ^ 2 + z = t * a⁻¹ ^ 2 := by
  obtain ⟨x, equation⟩ := root
  refine ⟨a⁻¹ * x, ?_⟩
  rw [← equation]
  unfold quadratic
  field_simp

omit [CharP K 2] in
theorem inverse_scales (u v c : K) (nonzeroU : u ≠ 0) (nonzeroV : v ≠ 0)
    (product : u * v = c) : v * c⁻¹ = u⁻¹ ∧ u * c⁻¹ = v⁻¹ := by
  rw [← product]
  constructor <;> field_simp

end BulksketchBridge.AffineQuartic
