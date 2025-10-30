import Lemma.Int.EqNegToNatNeg.of.Le_0
import Lemma.Nat.Le.of.Lt
open Int Nat


@[main]
private lemma main
  {z : ℤ}
-- given
  (h : z < 0) :
-- imply
  -(-z).toNat = z := 
-- proof
  EqNegToNatNeg.of.Le_0 (Le.of.Lt h)


-- created on 2025-10-30
