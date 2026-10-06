import sympy.Basic


@[main]
private lemma main
  {n u i j : ℤ}
-- given
  (h₀ : j ≥ i)
  (h₁ : i ≥ n - min n u)
  (h₂ : j < n) :
-- imply
  j - i ∈ Set.Ico 0 u := by
-- proof
  have h₃ : j - i < min n u := by omega
  exact ⟨sub_nonneg.mpr h₀, lt_of_lt_of_le h₃ (min_le_right n u)⟩


-- created on 2022-01-02
