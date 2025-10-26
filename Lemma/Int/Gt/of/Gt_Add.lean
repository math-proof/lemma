import Lemma.Nat.Gt.of.Gt.Ge
open Nat


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
  {n : ℕ}
-- given
  (h : x > y + n) :
-- imply
  x > y := by
-- proof
  have : y + n ≥ y := by
    simp
  apply Gt.of.Gt.Ge h this


-- created on 2025-04-27
