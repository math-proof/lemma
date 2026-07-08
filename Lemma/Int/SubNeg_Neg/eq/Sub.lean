import Lemma.Int.Add.eq.Sub_Neg
import Lemma.Nat.Sub.eq.AddNeg
open Int Nat


@[main, comm]
private lemma main
  [AddCommGroup α]
-- given
  (a b : α) :
-- imply
  -a - -b = b - a := by
-- proof
  rw [Sub_Neg.eq.Add]
  rw [AddNeg.eq.Sub]


-- created on 2026-07-08
