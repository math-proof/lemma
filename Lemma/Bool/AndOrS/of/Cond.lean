import sympy.Basic


@[main]
private lemma main
  {q : Prop}
-- given
  (h : q)
  (p : Prop) :
-- imply
  (p ∨ q) ∧ (¬p ∨ q) := by
-- proof
  constructor <;>

    exact Or.inr h


-- created on 2018-01-03
