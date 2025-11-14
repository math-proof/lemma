import Lemma.Nat.Lt.of.Le.Lt
open Nat


@[main, comm 1]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
  {n : ℕ}
-- given
  (h : x + n < y) :
-- imply
  x < y :=
-- proof
  Lt.of.Le.Lt (by simp) h


-- created on 2025-04-27
