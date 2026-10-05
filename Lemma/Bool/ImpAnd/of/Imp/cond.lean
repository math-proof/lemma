import sympy.Basic


@[main]
private lemma main
  {p q c : Prop}
-- given
  (h : p → q) :
-- imply
  p ∧ c → q := by
-- proof
  intro hpc
  exact h hpc.1


-- created on 2019-03-22
