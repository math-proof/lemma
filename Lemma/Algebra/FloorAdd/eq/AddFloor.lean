import sympy.Basic


@[main, comm]
private lemma nat
  [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  [FloorRing R]
  (x : R)
  (d : ℕ) :
-- imply
  ⌊x + d⌋ = ⌊x⌋ + d := by
-- proof
  have := Int.floor_add_intCast x d
  norm_cast at this


@[main, comm]
private lemma main
  [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  [FloorRing R]
  (x : R)
  (d : ℤ) :
-- imply
  ⌊x + d⌋ = ⌊x⌋ + d :=
-- proof
  Int.floor_add_intCast x d


-- created on 2025-03-04
-- updated on 2025-04-04
