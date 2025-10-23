import Lemma.Int.Sub.eq.Add_Neg
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.Add
open Nat Int


@[main, comm]
private lemma main
  [AddCommGroup α]
  {a b c : α} :
-- imply
  a - b + c = a + c - b := by
-- proof
  rw [Sub.eq.Add_Neg]
  rw [AddAdd.eq.Add_Add]
  rw [Add.comm (b := c)]
  rw [Add_Add.eq.AddAdd]
  rw [Add_Neg.eq.Sub]


-- created on 2025-03-04
-- updated on 2025-04-04
