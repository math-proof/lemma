import sympy.Basic


@[main]
private lemma left
-- given
  (h : p → f ∧ g) :
-- imply
  p → f := by
-- proof
  intro hp
  exact (h hp).left


@[main]
private lemma main
-- given
  (h : p → f ∧ g) :
-- imply
  p → g := by
-- proof
  intro hp
  exact (h hp).right


-- created on 2018-06-09
