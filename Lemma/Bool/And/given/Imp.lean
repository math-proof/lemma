import sympy.Basic


@[main]
private lemma main
  {p q r : Prop} :
-- imply
  (p → q) ∧ r ↔ (p ∨ ¬r) → q ∧ r := by
-- proof
  tauto


-- created on 2023-04-05
