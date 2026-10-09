import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n b : ℝ}
-- given
  (hn : 0 < n)
  (h : n ≤ b) :
-- imply
  1 / n ∈ Set.Ici (1 / b) :=
-- proof
  one_div_le_one_div_of_le hn h


-- created on 2023-10-04
