import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
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
-- updated on 2026-11-24
