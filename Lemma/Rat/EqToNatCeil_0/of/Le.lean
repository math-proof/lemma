import Lemma.Nat.OfNat.eq.Cast
import Lemma.Nat.LeCoeS.is.Le
import Lemma.Int.Sub.le.Zero.of.Le
import Lemma.Rat.Div.le.Zero.of.Le_0.Ge_0
import Lemma.Int.LeCeil.is.Le
import Lemma.Nat.LeCeil.is.Le
import Lemma.Int.EqToNat_0.of.Le_0
open Int Nat Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {a b d : ℕ}
-- given
  (h : a ≤ b) :
-- imply
  ⌈(a - b : α) / d⌉.toNat = 0 := by
-- proof
  have h := LeCoeS.of.Le (R := α) h
  have h := Sub.le.Zero.of.Le h
  have h_Ge_0 : (d : α) ≥ 0 := by simp
  have h_Le := Div.le.Zero.of.Le_0.Ge_0 h h_Ge_0
  apply EqToNat_0.of.Le_0
  apply Nat.LeCeil.of.Le
  rwa [OfNat.eq.Cast] at h_Le



-- created on 2025-05-05
