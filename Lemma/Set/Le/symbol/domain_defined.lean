import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a b : ℝ}
-- given
  (h : x ∈ Set.Icc a b) :
-- imply
  a ≤ b :=
-- proof
  h.1.trans h.2


-- created on 2019-09-24
