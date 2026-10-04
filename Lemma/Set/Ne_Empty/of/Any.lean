import sympy.Basic


@[main]
private lemma main
  {S : Set α}
  {p : α → Prop}
-- given
  (h : ∃ e ∈ S, p e) :
-- imply
  S ≠ ∅ := by
-- proof
  obtain ⟨e, he, -⟩ := h
  exact Set.nonempty_iff_ne_empty.mp ⟨e, he⟩


-- created on 2021-01-16
