import sympy.Basic


@[main]
private lemma main
  {p : α → Prop}
-- given
  (h : ¬∀ x : α, p x) :
-- imply
  ∃ x : α, ¬p x := by
-- proof
  aesop


-- created on 2024-07-01
