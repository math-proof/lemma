import Lemma.Int.EqToNat.of.Ge_0
import Lemma.Nat.Ge.of.Gt
open Int Nat


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n > 0) :
-- imply
  n = n.toNat := by
-- proof
  have h := Ge.of.Gt h
  apply Eq_ToNat.of.Ge_0 h


-- created on 2025-05-04
