import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n i : ℕ}
-- given
  (h : i ∈ Finset.range n) :
-- imply
  i < n := by
-- proof
  rw [Finset.mem_range] at h
  -- After the rewrite, `h` directly provides the conclusion `i < n`, so we can use it to finish the proof.
  exact h


-- created on 2025-04-06
-- updated on 2025-04-07
