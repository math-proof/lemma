import sympy.Basic


@[path]
private lemma main
  {p q r : Prop}
-- given
  (hq : q)
  (h : p → r) :
-- imply
  q ∧ (q ∧ p → r) := by
-- proof
  refine ⟨hq, ?_⟩
  rintro ⟨_, hp⟩
  exact h hp


-- created on 2026-10-03
