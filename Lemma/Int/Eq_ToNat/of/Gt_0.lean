import Lemma.Int.EqToNat.of.Ge_0
import Lemma.Algebra.Ge.of.Gt
open Algebra Int


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
