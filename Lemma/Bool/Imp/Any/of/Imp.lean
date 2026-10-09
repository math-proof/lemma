import sympy.Basic


@[path]
private lemma main
  {p q : α → Prop}
-- given
  (h : ∀ x, p x → q x) :
-- imply
  (∃ x, p x) → ∃ x, q x := by
-- proof
  rintro ⟨x, hx⟩
  exact ⟨x, h x hx⟩


-- created on 2023-11-10
