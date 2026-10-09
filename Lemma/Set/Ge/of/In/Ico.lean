import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n b : ℤ}
-- given
  (h : b ≤ n) :
-- imply
  n ∈ Set.Ici b := by
-- proof
  exact h


-- created on 2021-09-02
