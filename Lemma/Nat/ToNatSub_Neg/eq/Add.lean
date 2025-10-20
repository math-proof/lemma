import Lemma.Int.Add.eq.Sub_Neg
import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Int.EqToNat
import Lemma.Nat.ToNatAdd.eq.Add
open Int Nat


@[main]
private lemma main
-- given
  (i d : ℕ) :
-- imply
  (i - -(d : ℤ)).toNat = i + d := by
-- proof
  rw [Sub_Neg.eq.Add]
  apply Nat.ToNatAdd.eq.Add


-- created on 2025-10-19
