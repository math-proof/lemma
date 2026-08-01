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


-- created on 2018-10-12
-- updated on 2025-10-01
