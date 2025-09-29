import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
-- given
  (n : ℕ) :
-- imply
  range (n + 1) ∩ {n} = {n} := by
-- proof
  ext x
  simp [Finset.mem_range]


-- created on 2025-08-14
