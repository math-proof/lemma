import sympy.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [FloorRing α]
  {x y : α}
-- given
  (h : x = y) :
-- imply
  ⌈x⌉ = ⌈y⌉ := by
-- proof
  rw [h]


-- created on 2018-05-08
