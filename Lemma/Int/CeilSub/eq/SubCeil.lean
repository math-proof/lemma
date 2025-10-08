import sympy.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
  {d : ℤ} :
-- imply
  ⌈x - d⌉ = ⌈x⌉ - d :=
-- proof
  Int.ceil_sub_intCast x d


-- created on 2025-05-04
-- updated on 2025-10-08
