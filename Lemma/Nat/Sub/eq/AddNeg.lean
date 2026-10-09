import Lemma.Int.Sub.eq.Add_Neg
import Lemma.Nat.Add
open Nat Int


@[path, comm]
private lemma main
  [AddCommGroup α]
  {a b : α} :
-- imply
  a - b = -b + a := by
-- proof
  rw [Sub.eq.Add_Neg]
  rw [Add.comm]


-- created on 2025-03-30
