import sympy.Basic


@[path]
private lemma main
  {p q r : Prop} :
-- imply
  p ∧ ¬(q ∧ ¬r) ↔ p ∧ q ∧ r ∨ p ∧ ¬q := by
-- proof
  tauto


-- created on 2025-04-09
