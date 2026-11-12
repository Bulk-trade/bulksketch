import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Ring

namespace BulksketchBridge.AffineSubspaceAlgebra

open Polynomial

variable {F : Type} [Field F] [CharP F 2]

/-- New directions are pushed at the head, so this list is the reverse
of the prefix order used by the original triangular scratch table. -/
def spanWords : List F → Set F
  | [] => {0}
  | direction :: earlier => spanWords earlier ∪ (fun x => x + direction) '' spanWords earlier

noncomputable def annihilator : List F → Polynomial F
  | [] => X
  | direction :: earlier =>
    let previous := annihilator earlier
    previous ^ 2 + C (previous.eval direction) * previous

private theorem square_add (a b : F) : (a + b)^2 = a^2 + b^2 := by
  calc
    _ = a^2 + b^2 + (a*b + a*b) := by ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

private theorem twice_translate (x b : F) : (x + b) + b = x := by
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem annihilator_eval_add (basis : List F) (x y : F) :
    (annihilator basis).eval (x + y) = (annihilator basis).eval x + (annihilator basis).eval y := by
  induction basis with
  | nil => simp [annihilator]
  | cons direction earlier ih =>
    simp only [annihilator, eval_add, eval_pow, eval_mul, eval_C, ih, square_add]
    ring

/-- The triangular recurrence used by affine::subspaces gives the
vanishing polynomial for exactly the binary span of its directions. -/
theorem annihilator_zero (basis : List F) (x : F) :
    (annihilator basis).eval x = 0 ↔ x ∈ spanWords basis := by
  induction basis generalizing x with
  | nil => simp [annihilator, spanWords]
  | cons direction earlier ih =>
    have eval :
        (annihilator (direction :: earlier)).eval x =
          (annihilator earlier).eval x *
            ((annihilator earlier).eval x + (annihilator earlier).eval direction) := by
      simp only [annihilator, eval_add, eval_pow, eval_mul, eval_C]
      ring
    rw [eval, mul_eq_zero, ← annihilator_eval_add earlier x direction, ih x, ih (x + direction)]
    simp only [spanWords, Set.mem_union, Set.mem_image]
    constructor
    · rintro (old | shifted)
      · exact Or.inl old
      · exact Or.inr ⟨x + direction, shifted, twice_translate x direction⟩
    · rintro (old | ⟨point, old, exactPoint⟩)
      · exact Or.inl old
      · exact Or.inr (by rw [← exactPoint, twice_translate]; exact old)

def coset (base : F) (basis : List F) : Set F :=
  {point | point + base ∈ spanWords basis}

noncomputable def splitter (base : F) (basis : List F) : Polynomial F :=
  annihilator basis + C ((annihilator basis).eval base)

/-- The exact source splitter formula identifies membership of one
child coset. This remains true after reduction at every factor root. -/
theorem splitter_zero (base point : F) (basis : List F) :
    (splitter base basis).eval point = 0 ↔ point ∈ coset base basis := by
  simp only [splitter, eval_add, eval_C, ← annihilator_eval_add basis point base, coset, Set.mem_ofPred_eq,
    annihilator_zero]

theorem reduced_splitter_zero (base point : F) (basis : List F) (factor : Polynomial F)
    (root : factor.IsRoot point) :
    ((splitter base basis) %ₘ factor).eval point = 0 ↔ point ∈ coset base basis := by
  have vanishes : factor.eval point = 0 := root
  rw [modByMonic_eq_sub_mul_div, eval_sub, eval_mul, vanishes, zero_mul, sub_zero]
  exact splitter_zero base point basis

theorem coset_children (base direction point : F) (earlier : List F) :
    point ∈ coset base (direction :: earlier) ↔
      point ∈ coset base earlier ∨ point ∈ coset (base + direction) earlier := by
  simp only [coset, spanWords, Set.mem_ofPred_eq, Set.mem_union, Set.mem_image]
  constructor
  · rintro (same | ⟨old, admitted, exactPoint⟩)
    · exact Or.inl same
    · right
      rw [← add_assoc, ← exactPoint, twice_translate]
      exact admitted
  · rintro (same | moved)
    · exact Or.inl same
    · exact Or.inr ⟨point + (base + direction), moved, by
        rw [← add_assoc point base direction, twice_translate]⟩

theorem children_disjoint (base direction : F) (earlier : List F)
    (newDirection : direction ∉ spanWords earlier) :
    Disjoint (coset base earlier) (coset (base + direction) earlier) := by
  rw [Set.disjoint_left]
  intro point same moved
  change point + base ∈ spanWords earlier at same
  change point + (base + direction) ∈ spanWords earlier at moved
  have first := (annihilator_zero earlier (point + base)).mpr same
  rw [← add_assoc] at moved
  have second := (annihilator_zero earlier ((point + base) + direction)).mpr moved
  rw [annihilator_eval_add earlier (point + base) direction, first, zero_add] at second
  exact newDirection ((annihilator_zero earlier direction).mp second)


end BulksketchBridge.AffineSubspaceAlgebra
