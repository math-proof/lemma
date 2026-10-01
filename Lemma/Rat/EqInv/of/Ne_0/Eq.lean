import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  {f g : ℝ → ℝ}
-- given
  (_h₀ : f x ≠ 0)
  (h₁ : f x = g x) :
-- imply
  1 / f x = 1 / g x := by
-- proof
  rw [h₁]


-- created on 2020-06-18
