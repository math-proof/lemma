import sympy.sets.sets
import Lemma.Basic


@[main]
private lemma main
-- given
  (n : ℕ) :
-- imply
  range (n + 1) \ {n} = range n := by
-- proof
  rw [Finset.range_succ]
  aesop


-- created on 2025-08-14
