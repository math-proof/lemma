import sympy.Basic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p → q)
  (r : Prop):
-- imply
  r ∧ p → q := by
-- proof
  intro ⟨hr, hp⟩
  exact h hp


-- created on 2025-07-20
-- updated on 2025-10-01
