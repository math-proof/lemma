import Lemma.Nat.EqCoeS.is.Eq
import Lemma.Int.EqToNat.of.Ge_0
import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Int.ToNatNeg.eq.Neg.of.Le_0
import Lemma.Algebra.Sub.eq.AddNeg
import Lemma.Algebra.Sub.ge.Zero.of.Ge
open Algebra Int Nat


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n ≤ 0)
  (m : ℕ) :
-- imply
  (-n).toNat + m = (m - n).toNat := by
-- proof
  apply Eq.of.EqCoeS (R := ℤ)
  rw [EqToNat.of.Ge_0]
  ·
    rw [CoeAdd.eq.AddCoeS]
    rw [ToNatNeg.eq.Neg.of.Le_0 h]
    rw [AddNeg.eq.Sub]
  ·
    apply Sub.ge.Zero.of.Ge
    linarith


-- created on 2025-07-14
