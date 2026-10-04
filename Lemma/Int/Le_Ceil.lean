import sympy.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
-- given
  (x : α) :
-- imply
  x ≤ ⌈x⌉ :=
-- proof
  Int.le_ceil x


-- created on 2018-10-28
