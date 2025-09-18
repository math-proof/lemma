import Lemma.Basic


@[main, comm]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  (x : α)
  (d : ℤ) :
-- imply
  ⌈x + d⌉ = ⌈x⌉ + d :=
-- proof
  Int.ceil_add_int x d


-- created on 2025-03-04
