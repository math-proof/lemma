import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → ℕ → ℂ} :
-- imply
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, x i j =
    ∑ i ∈ Finset.range n, x i i +
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, (x i j + x j i) := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib] at *
    linear_combination ih


-- created on 2026-10-11
-- updated on 2026-10-12
