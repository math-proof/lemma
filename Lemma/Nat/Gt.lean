import sympy.sets.sets
import sympy.Basic


@[path]
private lemma symbol.domain_defined
  {a b x : ℝ}
-- given
  (h : x ∈ Set.Ico a b) :
-- imply
  b > a := by
-- proof
  exact lt_of_le_of_lt h.1 h.2


-- created on 2026-09-27
