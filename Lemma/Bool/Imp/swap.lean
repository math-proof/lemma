import sympy.Basic


@[path]
private lemma main
  {A p q : Prop} :
-- imply
  (A → p → q) → p → A → q := by
-- proof
  intro h hp ha
  exact h ha hp


-- created on 2019-10-06
