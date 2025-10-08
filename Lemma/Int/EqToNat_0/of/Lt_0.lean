import Lemma.Algebra.Le.of.Lt
import Lemma.Int.EqToNat_0.of.Le_0
open Algebra Int


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n < 0) :
-- imply
  n.toNat = 0 := by
-- proof
  have h := Le.of.Lt h
  apply EqToNat_0.of.Le_0 h


-- created on 2025-05-05
