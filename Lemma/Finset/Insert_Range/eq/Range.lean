import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ} :
-- imply
  Finset.range (n + 1) = insert n (Finset.range n) := by
-- proof
  rw [Finset.range_add_one]


-- created on 2018-04-24
