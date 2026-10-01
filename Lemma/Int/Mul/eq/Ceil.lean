import sympy.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {x : α} :
-- imply
  -⌊x⌋ = ⌈-x⌉ :=
-- proof
  Int.ceil_neg.symm


-- created on 2026-09-27
