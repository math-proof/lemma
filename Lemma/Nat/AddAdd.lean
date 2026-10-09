import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
open Nat


@[path]
private lemma Comm
  [AddCommSemigroup α]
-- given
  (a b c : α) :
-- imply
  a + b + c = a + c + b := by
-- proof
  repeat rw [Add.comm (b := c)]
  rw [Add_Add.eq.AddAdd]


@[path, comm]
private lemma rotate
  [AddCommSemigroup α]
-- given
  (a b c : α) :
-- imply
  a + b + c = b + c + a := by
-- proof
  rw [AddAdd.eq.Add_Add]
  rw [Add.comm]


@[path, comm]
private lemma swap
  [AddCommSemigroup α]
-- given
  (a b c : α) :
-- imply
  a + b + c = b + a + c := by
-- proof
  grind


-- created on 2025-06-06
