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
  sorry


-- created on 2026-10-11
