import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.Hinge
open MetaMathlibExt


/--
[hinge_opposite_side_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Hinge.lean)
-/
@[path]
private lemma hinge_opposite_side_sq_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {A B C : V} :
-- imply
  ‖C - B‖ ^ 2 =
      ‖C - A‖ ^ 2 - 2 * inner ℝ (C - A) (B - A) + ‖B - A‖ ^ 2 := by
-- proof
  apply MetaMathlibExt.hinge_opposite_side_sq A B C

/--
[hinge_sq_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Hinge.lean)
-/
@[path]
private lemma hinge_sq_lt_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {A B C D E F : V}
-- given
  (hAB : ‖B - A‖ = ‖E - D‖)
  (hAC : ‖C - A‖ = ‖F - D‖)
  (hinner : inner ℝ (B - A) (C - A) < inner ℝ (E - D) (F - D)) :
-- imply
  ‖F - E‖ ^ 2 < ‖C - B‖ ^ 2 := by
-- proof
  apply MetaMathlibExt.hinge_sq_lt A B C D E F hAB hAC hinner

/--
[hinge_norm_lt_of_sq_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Hinge.lean)
-/
@[path]
private lemma hinge_norm_lt_of_sq_lt_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {x y : V}
-- given
  (h : ‖x‖ ^ 2 < ‖y‖ ^ 2) :
-- imply
  ‖x‖ < ‖y‖ := by
-- proof
  apply MetaMathlibExt.hinge_norm_lt_of_sq_lt h

/--
[hinge_theorem_of_inner_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Hinge.lean)
-/
@[path]
private lemma hinge_theorem_of_inner_lt_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {A B C D E F : V}
-- given
  (hAB : ‖B - A‖ = ‖E - D‖)
  (hAC : ‖C - A‖ = ‖F - D‖)
  (hinner : inner ℝ (B - A) (C - A) < inner ℝ (E - D) (F - D)) :
-- imply
  ‖F - E‖ < ‖C - B‖ := by
-- proof
  apply MetaMathlibExt.hinge_theorem_of_inner_lt A B C D E F hAB hAC hinner

/--
[hinge_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Hinge.lean)
-/
@[path]
private lemma hinge_theorem_eq
  :
-- imply
  ∀ (A B C D E F : EuclideanSpace ℝ (Fin 2)),
  B ≠ A → C ≠ A → C ≠ B → E ≠ D → F ≠ D → F ≠ E →
  (∀ t : ℝ, C - A ≠ t • (B - A)) →
  (∀ s : ℝ, F - D ≠ s • (E - D)) →
  ‖B - A‖ = ‖E - D‖ → ‖C - A‖ = ‖F - D‖ →
  inner ℝ (B - A) (C - A) < inner ℝ (E - D) (F - D) →
  ‖F - E‖ < ‖C - B‖ := by
-- proof
  apply MetaMathlibExt.hinge_theorem


-- created on 2026-10-20
