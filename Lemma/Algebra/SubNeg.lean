import Lemma.Int.Sub.eq.Add_Neg
import Lemma.Nat.Add
open Nat Int


@[main]
private lemma Comm
  [AddCommGroup α]
  {a b : α} :
-- imply
  -a - b = -b - a := by
-- proof
  rw [Sub.eq.Add_Neg]
  rw [Add.comm]
  rw [Add_Neg.eq.Sub]


-- created on 2025-06-06
