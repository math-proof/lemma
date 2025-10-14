import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
open Nat


@[main]
private lemma Comm
  [AddCommSemigroup α]
  {a b : α} :
-- imply
  a + (b + c) = b + (a + c) := by
-- proof
  rw [Add_Add.eq.AddAdd]
  rw [Add.comm (b := b)]
  rw [AddAdd.eq.Add_Add]


-- created on 2025-07-18
