import sympy.Basic


@[main, comm]
private lemma main
  [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  [FloorRing R]
-- given
  (x : R)
  (d : ℤ) :
-- imply
  ⌊x + d⌋ = ⌊x⌋ + d :=
-- proof
  Int.floor_add_intCast x d


-- created on 2025-03-04
-- updated on 2025-10-08
