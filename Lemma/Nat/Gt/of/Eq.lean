import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h : a = b) :
-- imply
  a > b - 1 := by
-- proof
  rw [h]
  linarith


@[main]
private lemma relax
  {a b upper : ℝ}
-- given
  (h₀ : a = b)
  (h₁ : b < upper) :
-- imply
  upper > a := by
-- proof
  rw [h₀]
  exact h₁


-- created on 2020-10-18
