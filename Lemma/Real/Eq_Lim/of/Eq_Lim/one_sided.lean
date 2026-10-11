import sympy.series.limits
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x₀ A : ℝ}
-- given
  (h : lim [x → x₀] f x = A) :
-- imply
  lim [x → x₀] f x = A := by
-- proof
  apply h


-- created on 2026-10-11
