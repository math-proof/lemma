import sympy.series.limits
import sympy.Basic


@[path]
private lemma main
  {f g : ℝ → ℝ}
  {x₀ A B : ℝ}
-- given
  (hf : lim [x → x₀] f x = A)
  (hg : lim [x → x₀] g x = B) :
-- imply
  lim [x → x₀] (f x * g x) = A * B := by
-- proof
  sorry


-- created on 2026-10-11
