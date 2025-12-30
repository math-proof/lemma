import sympy.Basic


@[main]
private lemma main
  {p : α → Prop}
-- given
  (h : ∀ x : α, p x) :
-- imply
  ¬∃ x : α, ¬p x := by
-- proof
  push_neg
  exact h


-- created on 2025-04-06
