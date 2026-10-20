import sympy.series.limits
import sympy.Basic


@[path]
private lemma main
  {f g : ℝ → ℝ}
  {x₀ A B : ℝ}
-- given
  (h₀ : lim [x → x₀] f x = A)
  (h₁ : lim [x → x₀] g x = B) :
-- imply
  lim [x → x₀] (f x + g x) = A + B := by
-- proof
  apply h₀.add h₁


-- created on 2020-05-04
-- updated on 2026-10-17
