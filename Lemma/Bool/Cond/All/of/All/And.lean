import sympy.Basic


@[main]
private lemma main
  {B : Set β}
  {c : Prop}
  {g : β → Prop}
-- given
  (h₀ : ∀ y ∈ B, c ∧ g y)
  (h₁ : B.Nonempty) :
-- imply
  c ∧ ∀ y ∈ B, g y := by
-- proof
  obtain ⟨y, hy⟩ := h₁
  exact ⟨(h₀ y hy).1, fun y hy => (h₀ y hy).2⟩


-- created on 2026-09-27
