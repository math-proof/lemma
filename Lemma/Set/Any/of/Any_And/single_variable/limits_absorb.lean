import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {A B : Set α}
  {p : α → Prop}
-- given
  (h : ∃ x ∈ A, x ∈ B ∧ p x) :
-- imply
  ∃ x ∈ A ∩ B, p x := by
-- proof
  obtain ⟨x, hA, hB, hp⟩ := h
  exact ⟨x, ⟨hA, hB⟩, hp⟩


-- created on 2021-01-16
