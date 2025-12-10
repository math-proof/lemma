import sympy.Basic


@[main]
private lemma main
  [AddGroup α]
  [LinearOrder α]
-- given
  (a : α) :
-- imply
  |a| ≥ a := by
-- proof
  simp [le_abs]


-- created on 2025-12-10
