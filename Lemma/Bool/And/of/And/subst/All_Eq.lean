import sympy.Basic


@[main]
private lemma given
  {a b : ℕ → ℤ}
  {n : ℕ}
  {S : Set ℤ}
-- given
  (h₀ : ∀ i ∈ Finset.range n, a i = b i)
  (h₁ : ∑ i ∈ Finset.range n, b i ∈ S) :
-- imply
  (∀ i ∈ Finset.range n, a i = b i) ∧ ∑ i ∈ Finset.range n, a i ∈ S := by
-- proof
  refine ⟨h₀, ?_⟩
  rwa [Finset.sum_congr rfl h₀]


-- created on 2026-09-27
