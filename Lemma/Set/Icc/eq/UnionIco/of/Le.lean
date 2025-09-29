import sympy.sets.sets
import sympy.Basic


@[main]
private lemma MAIN
  [PartialOrder α]
  {a b : α}
-- given
  (h : a ≤ b) :
-- imply
  Icc a b = Ico a b ∪ ({b} : Set α) := by
-- proof
  ext x
  simp only [Set.mem_Icc, Set.mem_Ico, Set.mem_union]
  constructor
  ·
    intro hx
    rcases hx with ⟨hxa, hxb⟩
    by_cases h : x = b
    ·
      right
      exact h
    ·
      left
      exact ⟨hxa, lt_of_le_of_ne hxb h⟩
  ·
    intro hx
    cases hx with
    | inl h =>
      exact ⟨h.1, le_of_lt h.2⟩
    | inr h_in =>
      aesop


-- created on 2025-07-21
