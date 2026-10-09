import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {A B : Set α}
-- given
  (h : ∃ e ∈ A, e ∈ B) :
-- imply
  ∃ x ∈ B, x ∈ A := by
-- proof
  obtain ⟨e, hA, hB⟩ := h
  exact ⟨e, hB, hA⟩


-- created on 2020-09-04
