import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℝ}
-- given
  (h : ∀ i ∈ Finset.range n, f i ≥ g i) :
-- imply
  ∑ i ∈ Finset.range n, f i ≥ ∑ i ∈ Finset.range n, g i :=
-- proof
  Finset.sum_le_sum h


-- created on 2026-09-27
