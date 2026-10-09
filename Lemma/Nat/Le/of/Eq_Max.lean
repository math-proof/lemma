import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b M : ℝ}
-- given
  (h : max a b = M) :
-- imply
  a ≤ M := by
-- proof
  exact h ▸ le_max_left a b


-- created on 2023-04-23
