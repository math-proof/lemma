import sympy.Basic


@[main, comm]
private lemma main
  [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  [FloorRing R]
-- given
  (x : R)
  (d : ℕ) :
-- imply
  ⌊x + d⌋ = ⌊x⌋ + d := by
-- proof
  have := Int.floor_add_intCast x d
  norm_cast at this


-- created on 2025-10-08
