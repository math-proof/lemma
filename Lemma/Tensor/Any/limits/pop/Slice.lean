import sympy.Basic


@[main]
private lemma main
  {m : ℕ}
  {p : (Fin (m + 1) → β) → Prop} :
-- imply
  (∃ v : Fin (m + 1) → β, p v) ↔ ∃ v : Fin m → β, ∃ b : β, p (Fin.snoc v b) := by
-- proof
  constructor
  ·
    intro ⟨v, h⟩
    exact ⟨Fin.init v, v (Fin.last m), by rwa [Fin.snoc_init_self]⟩
  ·
    intro ⟨v, b, h⟩
    exact ⟨_, h⟩


-- created on 2023-07-02
