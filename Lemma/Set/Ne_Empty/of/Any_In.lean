import sympy.Basic


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : ∃ e ∈ A, e ∈ B) :
-- imply
  B ≠ ∅ := by
-- proof
  obtain ⟨e, -, he⟩ := h
  exact Set.nonempty_iff_ne_empty.mp ⟨e, he⟩


-- created on 2019-12-24
