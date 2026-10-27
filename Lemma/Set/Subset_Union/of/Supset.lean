import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {A B C : Set α}
-- given
  (h₀ : A ⊆ B ∪ C)
  (h₁ : Disjoint A C) :
-- imply
  A ⊆ B := by
-- proof
  intro x hx
  cases h₀ hx with
  | inl hxB => exact hxB
  | inr hxC => exact (h₁.le_bot ⟨hx, hxC⟩).elim


-- created on 2023-06-01
-- updated on 2026-10-26
