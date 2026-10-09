import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
-- given
  (n : ℕ) :
-- imply
  range (n + 1) \ {n} = range n := by
-- proof
  rw [Finset.range_add_one]
  aesop


-- created on 2025-08-14
