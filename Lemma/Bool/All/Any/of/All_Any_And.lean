import sympy.Basic


@[path]
private lemma main
  {A : Set α}
  {B : Set β}
  {C : Set γ}
  {p q : α → β → γ → Prop}
-- given
  (h : ∀ x ∈ A, ∃ y ∈ B, ∀ z ∈ C, p x y z ∧ q x y z) :
-- imply
  ∀ x ∈ A, ∃ y ∈ B, ∀ z ∈ C, p x y z := by
-- proof
  intro x hx
  obtain ⟨y, hy, hz⟩ := h x hx
  exact ⟨y, hy, fun z hzC => (hz z hzC).1⟩


-- created on 2018-12-25
