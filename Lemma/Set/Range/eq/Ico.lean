import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ} :
-- imply
  range n = Finset.Ico 0 n := by
-- proof
  -- Use the extensionality principle to show set equality.
  ext k
  -- Simplify the membership conditions using known lemmas.
  simp [Finset.mem_range]


-- created on 2025-04-06
