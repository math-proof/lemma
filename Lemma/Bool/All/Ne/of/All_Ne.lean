import sympy.Basic


@[main]
private lemma main
  [DecidableEq β]
  {n : ℕ}
  {x : ℕ → β}
-- given
  (h : ∀ i < n, ∀ j < i, x i ≠ x j) :
-- imply
  ∀ i < n, ∀ j ∈ Finset.range n \ {i}, x i ≠ x j := by
-- proof
  intro i hi j hj
  simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hj
  rcases Nat.lt_or_gt_of_ne hj.2 with h' | h'
  ·
    exact h i hi j h'
  ·
    exact (h j hj.1 i h').symm


-- created on 2026-09-27
