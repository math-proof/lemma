import Mathlib
import sympy.Basic


namespace MetaMathlibExt

/--
[hinge_opposite_side_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Hinge.lean)
-/
@[path]
private lemma hinge_opposite_side_sq {V : Type*} [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] (A B C : V) :
  ‖C - B‖ ^ 2 =
    ‖C - A‖ ^ 2 - 2 * inner ℝ (C - A) (B - A) + ‖B - A‖ ^ 2 := by
  rw [show C - B = (C - A) - (B - A) by abel]
  exact norm_sub_sq_real (C - A) (B - A)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hinge_sq_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Hinge.lean)
-/
@[path]
private lemma hinge_sq_lt {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (A B C D E F : V)
  (hAB : ‖B - A‖ = ‖E - D‖) (hAC : ‖C - A‖ = ‖F - D‖)
  (hinner : inner ℝ (B - A) (C - A) < inner ℝ (E - D) (F - D)) :
  ‖F - E‖ ^ 2 < ‖C - B‖ ^ 2 := by
  rw [hinge_opposite_side_sq D E F, hinge_opposite_side_sq A B C]
  rw [real_inner_comm (E - D) (F - D), real_inner_comm (B - A) (C - A)]
  rw [← hAC, ← hAB]
  linarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hinge_norm_lt_of_sq_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Hinge.lean)
-/
@[path]
private lemma hinge_norm_lt_of_sq_lt {V : Type*} [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] {x y : V}
  (h : ‖x‖ ^ 2 < ‖y‖ ^ 2) : ‖x‖ < ‖y‖ :=
  (sq_lt_sq₀ (norm_nonneg x) (norm_nonneg y)).mp h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hinge_theorem_of_inner_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Hinge.lean)
-/
@[path]
lemma hinge_theorem_of_inner_lt
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {A B C D E F : V}
-- given
  (hAB : ‖B - A‖ = ‖E - D‖)
  (hAC : ‖C - A‖ = ‖F - D‖)
  (hinner : inner ℝ (B - A) (C - A) < inner ℝ (E - D) (F - D)) :
-- imply
  ‖F - E‖ < ‖C - B‖ :=
-- proof
  hinge_norm_lt_of_sq_lt (hinge_sq_lt A B C D E F hAB hAC hinner)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hinge_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Hinge.lean)
-/
@[path]
lemma hinge_theorem
  :
-- imply
  ∀ (A B C D E F : EuclideanSpace ℝ (Fin 2)),
    B ≠ A → C ≠ A → C ≠ B → E ≠ D → F ≠ D → F ≠ E →
    (∀ t : ℝ, C - A ≠ t • (B - A)) →
    (∀ s : ℝ, F - D ≠ s • (E - D)) →
    ‖B - A‖ = ‖E - D‖ → ‖C - A‖ = ‖F - D‖ →
    inner ℝ (B - A) (C - A) < inner ℝ (E - D) (F - D) →
    ‖F - E‖ < ‖C - B‖ :=
-- proof
  fun A B C D E F _ _ _ _ _ _ _ _ => hinge_theorem_of_inner_lt A B C D E F

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
