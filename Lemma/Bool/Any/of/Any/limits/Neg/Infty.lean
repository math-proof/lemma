import sympy.Basic


@[main]
private lemma given
  {f : ℤ → Prop}
-- given
  (h : ∃ i, f (-i)) :
-- imply
  ∃ i, f i := by
-- proof
  obtain ⟨i, hf⟩ := h
  exact ⟨-i, hf⟩


-- created on 2019-02-13
