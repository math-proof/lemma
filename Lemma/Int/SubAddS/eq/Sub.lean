import Lemma.Int.EqSubAdd
import Lemma.Int.Sub_Add.eq.SubSub
import Lemma.Nat.Add
open Nat Int


@[main]
private lemma main
  [AddCommGroup α]
-- given
  (a b : α) :
-- imply
  a + c - (b + c) = a - b := by
-- proof
  rw [Add.comm (a := b)]
  rw [Sub_Add.eq.SubSub]
  rw [EqSubAdd]


@[main]
private lemma left
  [AddCommGroup α]
-- given
  (a b : α) :
-- imply
  c + a - (c + b) = a - b := by
-- proof
  rw [Sub_Add.eq.SubSub]
  rw [EqSubAdd.left]


-- created on 2025-12-11
