/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/Euclidean/Hinge.lean -/


import Lemma.Set.Euclidean.Hinge


namespace MetaMathlibExt

-- The generalized hinge theorem also applies to collinear configurations.
example : ‖(2 : ℝ) - 1‖ < ‖(-2 : ℝ) - 1‖ := by
  apply hinge_theorem_of_inner_lt (A := (0 : ℝ)) (B := 1) (C := -2)
    (D := 0) (E := 1) (F := 2)
  · norm_num
  · norm_num
  · norm_num

-- The strict hinge comparison rules out equal opposite-side lengths.
example (A B C D E F : EuclideanSpace ℝ (Fin 2))
    (hBA : B ≠ A) (hCA : C ≠ A) (hCB : C ≠ B)
    (hED : E ≠ D) (hFD : F ≠ D) (hFE : F ≠ E)
    (hABC : ∀ t : ℝ, C - A ≠ t • (B - A))
    (hDEF : ∀ s : ℝ, F - D ≠ s • (E - D))
    (hAB : ‖B - A‖ = ‖E - D‖) (hAC : ‖C - A‖ = ‖F - D‖)
    (hinner : inner ℝ (B - A) (C - A) < inner ℝ (E - D) (F - D)) :
    ‖F - E‖ ≠ ‖C - B‖ := by
  exact ne_of_lt
    (hinge_theorem A B C D E F hBA hCA hCB hED hFD hFE hABC hDEF hAB hAC hinner)

end MetaMathlibExt
