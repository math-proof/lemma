import sympy.Basic


@[main]
private lemma main
  [GroupWithZero α]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  a / a = 1 := by
-- proof
  simp [h]


-- created on 2024-07-01
