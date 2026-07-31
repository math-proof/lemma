import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
open Nat


@[main]
private lemma Comm
  [AddCommSemigroup α]
-- given
  (a b c : α) :
-- imply
  a + b + c = a + c + b := by
-- proof
  repeat rw [Add.comm (b := c)]
  rw [Add_Add.eq.AddAdd]


@[main, comm]
private lemma rotate
  [AddCommSemigroup α]
-- given
  (a b c : α) :
-- imply
  a + b + c = b + c + a := by
-- proof
  rw [AddAdd.eq.Add_Add]
  rw [Add.comm]


-- created on 2025-06-06
