import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x M : ℝ}
-- given
  (h : x ∈ Set.Icc 0 M) :
-- imply
  x * x ≤ M * M :=
-- proof
  mul_self_le_mul_self h.1 h.2


-- created on 2021-03-10
