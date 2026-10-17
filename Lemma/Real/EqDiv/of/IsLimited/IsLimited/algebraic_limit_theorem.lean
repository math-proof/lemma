import sympy.series.limits
import sympy.Basic


@[path]
private lemma main
  {f g : ℝ → ℝ}
  {x₀ A B : ℝ}
-- given
  (h₀ : lim [x → x₀] f x = A)
  (h₁ : lim [x → x₀] g x = B)
  (h₂ : B ≠ 0) :
-- imply
  lim [x → x₀] (f x / g x) = A / B := by
-- proof
  apply h₀.div h₁ h₂


-- created on 2026-10-11
-- updated on 2026-10-17
