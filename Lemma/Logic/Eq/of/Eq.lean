import sympy.Basic


@[main]
private lemma main
  [Coe α β]
  {x y : α}
-- given
  (h : x = y) :
-- imply
  (x : β) = (y : β) := by
-- proof
  rw [h]


-- created on 2025-03-20
