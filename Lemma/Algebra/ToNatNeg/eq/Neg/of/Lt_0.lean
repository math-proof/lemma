import Lemma.Algebra.ToNatNeg.eq.Neg.of.Le_0
import Lemma.Algebra.Le.of.Lt
open Algebra


@[main]
private lemma main
  {z : ℤ}
-- given
  (h : z < 0) :
-- imply
  (-z).toNat = -z := by
-- proof
  have h := Le.of.Lt h
  apply ToNatNeg.eq.Neg.of.Le_0 h


-- created on 2025-10-01
