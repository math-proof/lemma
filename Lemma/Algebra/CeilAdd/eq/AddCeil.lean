import Lemma.Basic


@[main, comm]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  (x : α)
  (d : ℤ) :
-- imply
  ⌈x + d⌉ = ⌈x⌉ + d :=
-- proof
  Int.ceil_add_intCast x d


-- created on 2025-03-04
