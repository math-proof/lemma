import sympy.Basic


@[main]
private lemma given
  {A B : Set α}
  {x : α}
  [Decidable (x ∈ A)] [Decidable (x ∈ B)]
  {f g k : α → β}
  {p : β}
-- given
  (h : (if x ∈ A then f x else if x ∈ B then g x else k x) = p) :
-- imply
  (f x = p ∧ x ∈ A) ∨ (p = g x ∧ x ∈ B \ A) ∨ (p = k x ∧ x ∉ A ∪ B) := by
-- proof
  by_cases hA : x ∈ A
  ·
    rw [if_pos hA] at h
    exact Or.inl ⟨h, hA⟩
  ·
    rw [if_neg hA] at h
    by_cases hB : x ∈ B
    ·
      rw [if_pos hB] at h
      exact Or.inr (Or.inl ⟨h.symm, hB, hA⟩)
    ·
      rw [if_neg hB] at h
      exact Or.inr (Or.inr ⟨h.symm, fun hAB => hAB.elim hA hB⟩)


-- created on 2023-04-30
