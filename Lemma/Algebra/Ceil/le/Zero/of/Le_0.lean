import sympy.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
-- given
  (h : x ≤ 0) :
-- imply
  ⌈x⌉ ≤ 0 := by
-- proof
  exact Int.ceil_le.mpr (by simpa)


-- created on 2018-10-30
-- updated on 2026-08-20
