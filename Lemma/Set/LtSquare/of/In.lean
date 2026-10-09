import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a : ℝ}
-- given
  (h : x ∈ Set.Ioo (-a) a) :
-- imply
  x ^ 2 < a ^ 2 :=
-- proof
  sq_lt_sq' h.1 h.2


-- created on 2020-11-26
