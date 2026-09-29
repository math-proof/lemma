import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
-- given
  (h : x ∈ Set.Ico a b) :
-- imply
  x < b := by
-- proof
  exact h.2


@[main]
private lemma left_open
  {x a b : ℝ}
-- given
  (h : x ∈ Set.Ioc a b) :
-- imply
  a < x := by
-- proof
  exact h.1


-- created on 2026-09-27
