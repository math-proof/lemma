import Lemma.Algebra.EqSubAdd
open Algebra


@[main, comm]
private lemma main
  {x y d : ℕ}
-- given
  (h : d + x = y) :
-- imply
  y - x = d := by
-- proof
  rw [← h]
  rw [EqSubAdd.int]


-- created on 2025-04-16
-- updated on 2025-10-08
