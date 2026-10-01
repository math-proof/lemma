import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h : a = b)
  (d : ℝ) :
-- imply
  a / d = b / d ∨ d = 0 := by
-- proof
  exact Or.inl (by rw [h])


-- created on 2026-09-27
