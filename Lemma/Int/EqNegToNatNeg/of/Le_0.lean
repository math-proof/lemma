import Lemma.Int.ToNatNeg.eq.Neg.of.Le_0
open Int


@[main]
private lemma main
  {z : ℤ}
-- given
  (h : z ≤ 0) :
-- imply
  -(-z).toNat = z := by
-- proof
  simp [ToNatNeg.eq.Neg.of.Le_0 h]


-- created on 2025-10-30
