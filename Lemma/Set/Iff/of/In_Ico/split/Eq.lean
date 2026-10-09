import sympy.Basic


@[path]
private lemma main
  {x y : ℕ → α}
  {n m : ℕ}
-- given
  (h : n ∈ Set.Ico 1 m) :
-- imply
  (∀ i < m, x i = y i) ↔ (∀ i < n, x i = y i) ∧ ∀ i ∈ Set.Ico n m, x i = y i := by
-- proof
  simp only [Set.mem_Ico] at h ⊢
  constructor
  ·
    intro h'
    exact ⟨fun i hi => h' i (by omega), fun i hi => h' i hi.2⟩
  ·
    rintro ⟨h₁, h₂⟩ i hi
    by_cases hin : i < n
    ·
      exact h₁ i hin
    ·
      exact h₂ i ⟨by omega, hi⟩


-- created on 2023-03-26
