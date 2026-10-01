import sympy.Basic


@[main]
private lemma unshift.given
  {g : ℤ → Prop}
  {a b : ℤ}
-- given
  (h₀ : a + 1 ≤ b)
  (h₁ : ∀ k ∈ Set.Ico (a - 1) b, g k) :
-- imply
  g (a - 1) ∧ ∀ k ∈ Set.Ico a b, g k := by
-- proof
  refine ⟨h₁ (a - 1) (by simp only [Set.mem_Ico]; omega), fun k hk => h₁ k ?_⟩
  simp only [Set.mem_Ico] at hk ⊢
  omega


-- created on 2019-03-12
