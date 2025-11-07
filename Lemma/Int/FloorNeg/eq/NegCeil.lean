import sympy.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α} :
-- imply
  ⌊-x⌋ = -⌈x⌉ := 
-- proof
  Int.floor_neg


-- created on 2025-11-07
