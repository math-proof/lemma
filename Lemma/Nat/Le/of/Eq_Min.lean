import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b M : ℝ}
-- given
  (h : min a b = M) :
-- imply
  M ≤ a := by
-- proof
  exact h ▸ min_le_left a b


-- created on 2019-04-24
