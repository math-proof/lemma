import sympy.Basic


@[main, comm]
private lemma main
  [AddGroup α]
  (a b : α) :
-- imply
  a - b = -(b - a) := by
-- proof
  simp


-- created on 2024-11-29
