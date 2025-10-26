import sympy.Basic


@[main]
private lemma main
  [Zero α]
  [One α]
  [NeZero (1 : α)]
  {a : α}
-- given
  (h : a = 0) :
-- imply
  a ≠ 1 := by
-- proof
  rw [h]
  apply zero_ne_one


-- created on 2025-04-20
