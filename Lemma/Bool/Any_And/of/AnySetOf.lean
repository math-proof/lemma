import sympy.concrete.quantifier
import sympy.Basic


@[main]
private lemma main
  {p q : α → Prop}
-- given
  (h : ∃ x | p x, q x) :
-- imply
  ∃ x, p x ∧ q x := by
-- proof
  assumption


-- created on 2025-04-27
