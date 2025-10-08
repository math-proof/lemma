import Lemma.Int.Add_ToNatNeg.eq.ToNatSub.of.Le_0
import Lemma.Nat.Le.of.Lt
open Int Nat


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n < 0)
  (m : ℕ) :
-- imply
  (-n).toNat + m = (m - n).toNat := by
-- proof
  apply Add_ToNatNeg.eq.ToNatSub.of.Le_0
  apply Le.of.Lt h


-- created on 2025-07-14
