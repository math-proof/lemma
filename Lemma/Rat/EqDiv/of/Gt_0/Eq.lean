import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  {f g h : ℝ → ℝ}
-- given
  (h₀ : f x > 0)
  (h₁ : g x * f x = h x * f x + x) :
-- imply
  g x = h x + x / f x := by
-- proof
  have hf := h₀.ne'
  field_simp
  linarith


-- created on 2019-04-01
