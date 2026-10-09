import Mathlib.Analysis.InnerProductSpace.PiL2
import sympy.Basic


@[path]
private lemma main
  {x : EuclideanSpace ℝ (Fin n)} :
-- imply
  ‖x‖ = √(∑ i, |x i| ^ 2) := by
-- proof
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs]


-- created on 2020-12-25
