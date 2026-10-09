import sympy.Basic


@[path]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {x y : α}
-- given
  (h : x ≤ y) :
-- imply
  ⌈x⌉ ≤ ⌈y⌉ :=
-- proof
  Int.ceil_mono h


-- created on 2021-12-27
