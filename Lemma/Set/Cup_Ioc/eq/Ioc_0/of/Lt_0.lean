import Lemma.Set.CupIcoNeg_0.eq.IocNeg_0
import Lemma.Int.ToNatNeg.eq.Neg.of.Lt_0
import Lemma.Int.EqNegNeg
import Lemma.Int.CoeCoe.eq.Coe
open Set Int


@[main]
private lemma main
  [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  {n : ℤ}
-- given
  (h : n < 0) :
-- imply
  ⋃ k ∈ Ico n 0, Ioc (k : R) (k + 1 : R) = Ioc (n : R) (0 : R) := by
-- proof
  have h_n := CupIcoNeg_0.eq.IocNeg_0 (R := R)
  specialize h_n (-n).toNat
  rw [ToNatNeg.eq.Neg.of.Lt_0 h] at h_n
  rw [EqNegNeg] at h_n
  rw [h_n]
  rw [Coe.eq.CoeCoe]
  rw [ToNatNeg.eq.Neg.of.Lt_0 h]
  simp


-- created on 2025-10-01
