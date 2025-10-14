import Lemma.Int.NegSucc.eq.NegAdd_1
import Lemma.Algebra.Add.eq.Sub_Neg
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
open Algebra Nat Int


@[main]
private lemma main
-- given
  (n a : ℕ) :
-- imply
  a - Int.negSucc n = a + 1 + n := by
-- proof
  rw [NegSucc.eq.NegAdd_1]
  rw [Sub_Neg.eq.Add]
  rw [Add.comm (b := 1)]
  rw [Add_Add.eq.AddAdd]


-- created on 2025-07-18
