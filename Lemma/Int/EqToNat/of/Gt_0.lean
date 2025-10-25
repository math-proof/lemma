import Lemma.Int.EqToNat.of.Ge_0
import Lemma.Nat.Ge.of.Gt
open Int Nat


@[main, comm]
private lemma main
  {n : ℤ}
-- given
  (h : n > 0) :
-- imply
  n.toNat = n :=
-- proof
  EqToNat.of.Ge_0 (Ge.of.Gt h)


-- created on 2025-05-04
-- updated on 2025-10-25
