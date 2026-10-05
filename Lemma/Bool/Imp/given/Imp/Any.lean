import sympy.Basic


@[main]
private lemma main
  {p q : α → Prop}
-- given
  (h : ∀ x, p x → q x) :
-- imply
  (∃ x, p x) → ∃ x, q x := by
-- proof
  intro hx
  obtain ⟨x, hpx⟩ := hx
  exact ⟨x, h x hpx⟩


-- created on 2023-11-10
