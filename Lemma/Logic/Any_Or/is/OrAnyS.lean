import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  {p q : α → Prop} :
-- imply
  (∃ x : α, p x ∨ q x) ↔ (∃ x : α, p x) ∨ (∃ x : α, q x) := by
-- proof
  constructor <;>
    intro h
  ·
    let ⟨x, hpq⟩ := h
    cases hpq with
    | inl hp =>
      exact Or.inl ⟨x, hp⟩
    | inr hq =>
      exact Or.inr ⟨x, hq⟩
  ·
    cases h with
    | inl h_p =>
      let ⟨x, hp⟩ := h_p
      exact ⟨x, Or.inl hp⟩
    | inr h_q =>
      let ⟨x, hq⟩ := h_q
      exact ⟨x, Or.inr hq⟩


@[main, comm, mp, mpr]
private lemma set
  {p q : α → Prop}
  {s : Set α}:
-- imply
  (∃ x ∈ s, p x ∨ q x) ↔ (∃ x ∈ s, p x) ∨ (∃ x ∈ s, q x) := by
-- proof
  rw [← main]
  aesop

-- created on 2024-07-01
-- updated on 2025-07-30
