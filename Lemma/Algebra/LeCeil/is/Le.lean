import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  (x : α)
  (n : ℤ) :
-- imply
  ⌈x⌉ ≤ n ↔ x ≤ n :=
-- proof
  Int.ceil_le


-- created on 2025-05-05
