import sympy.sets.sets
import Lemma.Bool.Ne.is.NotEq
open Bool


@[main]
private lemma main
  [PartialOrder α]
  {a b : α}
-- given
  (h : a < b) :
-- imply
  Ico a b = ({a} : Set α) ∪ Ioo a b := by
-- proof
  ext x
  simp only [Set.mem_Ico, Set.mem_Ioo, Set.mem_union]
  constructor
  ·
    intro hx
    rcases hx with
    ⟨hxa, hxb⟩
    by_cases h : x = a
    ·
      left
      exact h
    ·
      right
      have h := Ne.of.NotEq h
      exact ⟨lt_of_le_of_ne hxa h.symm, hxb⟩
  ·
    intro hx
    cases hx with
    | inl h_in =>
      aesop
    | inr h =>
      exact ⟨le_of_lt h.1, h.2⟩


-- created on 2025-07-21
