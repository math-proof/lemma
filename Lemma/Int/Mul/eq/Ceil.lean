import sympy.Basic


@[path]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {x : α} :
-- imply
  -⌊x⌋ = ⌈-x⌉ :=
-- proof
  Int.ceil_neg.symm


-- created on 2020-01-28
