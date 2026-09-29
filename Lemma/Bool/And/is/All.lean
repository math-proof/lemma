import sympy.Basic


@[main]
private lemma limits.push
  {f : ℤ → Prop}
  {a b : ℤ}
-- given
  (h : a ≤ b) :
-- imply
  (∀ i ∈ Set.Ico a b, f i) ∧ f b ↔ ∀ i ∈ Set.Ico a (b + 1), f i := by
-- proof
  constructor
  ·
    rintro ⟨h₁, h₂⟩ i hi
    simp only [Set.mem_Ico] at hi
    by_cases hib : i = b
    ·
      subst hib
      exact h₂
    ·
      exact h₁ i (by simp only [Set.mem_Ico]; omega)
  ·
    intro h'
    exact ⟨fun i hi => h' i (by simp only [Set.mem_Ico] at hi ⊢; omega), h' b (by simp only [Set.mem_Ico]; omega)⟩


@[main]
private lemma limits.unshift
  {f : ℤ → Prop}
  {a b : ℤ}
-- given
  (h : a ≤ b) :
-- imply
  (∀ i ∈ Set.Ico a b, f i) ∧ f (a - 1) ↔ ∀ i ∈ Set.Ico (a - 1) b, f i := by
-- proof
  constructor
  ·
    rintro ⟨h₁, h₂⟩ i hi
    simp only [Set.mem_Ico] at hi
    by_cases hia : i = a - 1
    ·
      subst hia
      exact h₂
    ·
      exact h₁ i (by simp only [Set.mem_Ico]; omega)
  ·
    intro h'
    exact ⟨fun i hi => h' i (by simp only [Set.mem_Ico] at hi ⊢; omega), h' (a - 1) (by simp only [Set.mem_Ico]; omega)⟩


-- created on 2026-09-27
