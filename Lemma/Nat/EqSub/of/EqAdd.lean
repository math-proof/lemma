import Lemma.Nat.EqSubAdd
open Nat


@[main, comm]
private lemma main
  {x y d : ℕ}
-- given
  (h : d + x = y) :
-- imply
  y - x = d := by
-- proof
  rw [← h]
  rw [EqSubAdd]


@[main, comm]
private lemma left
  {x y d : ℕ}
-- given
  (h : d + x = y) :
-- imply
  y - d = x := by
-- proof
  rw [← h]
  rw [EqSubAdd.left]


-- created on 2025-04-16
-- updated on 2025-10-08
