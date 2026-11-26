import Initialize.Tactic.Attr.Basic


@[path]
private lemma given
  {a b : ℕ → ℤ}
  {n : ℕ}
  {S : Set ℤ}
-- given
  (h₀ : ∀ i < n, a i = b i)
  (h₁ : ∑ i < n, b i ∈ S) :
-- imply
  (∀ i < n, a i = b i) ∧ ∑ i < n, a i ∈ S := by
-- proof
  refine ⟨h₀, ?_⟩
  have hsum : ∑ i < n, a i = ∑ i < n, b i := Finset.sum_congr rfl (fun i hi => h₀ i (by simpa using hi))
  simpa only [hsum] using h₁


-- created on 2019-05-02
-- updated on 2026-11-26
