import Mathlib.Analysis.InnerProductSpace.PiL2
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x y : EuclideanSpace ℝ (Fin n)} :
-- imply
  ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * @inner ℝ _ _ x y + ‖y‖ ^ 2 := by
-- proof
  simpa using norm_add_sq_real x y


-- created on 2023-06-24
-- updated on 2026-10-17
