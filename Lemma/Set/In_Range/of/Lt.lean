import sympy.Basic


@[main]
private lemma main
  {i n : ℕ}
-- given
  (h : i < n) :
-- imply
  i ∈ Finset.range n := by
-- proof
  -- Apply the lemma that connects membership in Finset.range n with the inequality i < n.
  rw [Finset.mem_range]
  -- Use the given hypothesis h : i < n to conclude the proof.
  exact h


-- created on 2025-04-26
