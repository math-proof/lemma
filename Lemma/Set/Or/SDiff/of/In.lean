import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {e : α}
  {A B : Set α}
-- given
  (h : e ∈ A ∪ B) :
-- imply
  e ∈ A ∨ e ∈ B \ A := by
-- proof
  obtain h | h := h
  ·
    exact Or.inl h
  ·
    if ha : e ∈ A then
      exact Or.inl ha
    else
      exact Or.inr ⟨h, ha⟩


-- created on 2021-03-13
