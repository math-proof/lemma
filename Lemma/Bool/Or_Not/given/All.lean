import sympy.Basic


@[main]
private lemma main
  {p : α → Prop}
  {y : α}
-- given
  (h : ∀ x, p x ∨ x = y) :
-- imply
  ∀ x, x ≠ y → p x := by
-- proof
  intro x hxy
  obtain hp | heq := h x
  · exact hp
  · exact False.elim (hxy heq)


-- created on 2018-12-02
