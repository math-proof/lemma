import Lemma.Int.LeCeil.is.Le
open Int


@[main, comm, mp, mpr]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  (x : α)
  (n : ℕ) :
-- imply
  ⌈x⌉ ≤ n ↔ x ≤ n := by
-- proof
  simp [LeCeil.is.Le]


-- created on 2025-11-08
