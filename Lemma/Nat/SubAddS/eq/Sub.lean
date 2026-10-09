import Lemma.Nat.Sub_Add.eq.SubSub
import Lemma.Nat.Add
import Lemma.Nat.EqSubAdd
open Nat


@[path]
private lemma main
-- given
  (a b : ℕ) :
-- imply
  a + c - (b + c) = a - b := by
-- proof
  rw [Add.comm (a := b)]
  rw [Sub_Add.eq.SubSub]
  rw [EqSubAdd]


-- created on 2025-11-15
