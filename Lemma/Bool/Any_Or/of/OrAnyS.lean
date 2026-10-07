import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {α : Type*}
  {A : Set α}
  {p q : α → Prop}
-- given
  (h : (∃ x ∈ A, p x) ∨ (∃ x ∈ A, q x)) :
-- imply
  ∃ x ∈ A, p x ∨ q x := by
-- proof
  obtain ⟨x, hx, hx'⟩ | ⟨x, hx, hx'⟩ := h
  · exact ⟨x, hx, Or.inl hx'⟩
  · exact ⟨x, hx, Or.inr hx'⟩


-- created on 2018-10-02
-- updated on 2023-05-11
