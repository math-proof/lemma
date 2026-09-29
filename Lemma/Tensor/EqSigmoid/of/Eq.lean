import sympy.tensor.lstm
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  {f g : ℝ → ℝ}
-- given
  (h : f x = g x) :
-- imply
  sigmoid (f x) = sigmoid (g x) := by
-- proof
  rw [h]


-- created on 2026-09-27
