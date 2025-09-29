import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
-- given
  (i n : ℕ) :
-- imply
  Ico i n = range n \ range i := by
-- proof
  -- Use the extensionality principle to show set equality.
  simp_all


@[main]
private lemma fin
-- given
  (i n : ℕ) :
-- imply
  Finset.Ico i n = range n \ range i := by
-- proof
  -- Use the extensionality principle to show set equality.
  ext k
  simp [Finset.mem_Ico, Finset.mem_range]
  rw [And.comm]


-- created on 2025-05-18
