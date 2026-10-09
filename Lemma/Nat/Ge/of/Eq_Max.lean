import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b M : ℝ}
-- given
  (h : max a b = M) :
-- imply
  M ≥ a := by
-- proof
  exact h ▸ le_max_left a b


-- created on 2019-04-23
