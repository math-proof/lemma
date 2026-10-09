import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a b : ℝ}
-- given
  (h : x ∈ Set.Ico a b) :
-- imply
  x < b := by
-- proof
  exact h.2


@[path]
private lemma left_open
  {x a b : ℝ}
-- given
  (h : x ∈ Set.Ioc a b) :
-- imply
  a < x := by
-- proof
  exact h.1


-- created on 2020-04-18
