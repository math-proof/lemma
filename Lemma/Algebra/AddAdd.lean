import Lemma.Nat.Add
import Lemma.Algebra.AddAdd.eq.Add_Add
open Algebra Nat


@[main]
private lemma Comm
  [AddCommSemigroup α]
  {a b : α} :
-- imply
  a + b + c = a + c + b := by
-- proof
  rw [Add.comm (b := c)]
  rw [Add.comm (b := c)]
  rw [Add_Add.eq.AddAdd]


@[main]
private lemma permute
  [AddCommSemigroup α]
  {a b c : α} :
-- imply
  a + b + c = b + c + a := by
-- proof
  rw [AddAdd.eq.Add_Add]
  rw [Add.comm]


-- created on 2025-06-06
