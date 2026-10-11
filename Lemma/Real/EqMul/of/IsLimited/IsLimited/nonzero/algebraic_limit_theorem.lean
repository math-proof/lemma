import sympy.series.limits
import sympy.Basic


@[path]
private lemma main
  {f g : ℝ → ℝ}
  {x₀ a b : ℝ}
-- given
  (ha : a ≠ 0)
  (hf : lim [x → x₀] f x = a)
  (hg : lim [x → x₀] g x = b) :
-- imply
  lim [x → x₀] (f x * g x) = a * b := by
-- proof
  sorry


-- created on 2026-10-11
