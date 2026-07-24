import Lemma.List.GetPermute__Neg.eq.Ite.of.GtLength
import Lemma.Int.EqNegToNatNeg.of.Lt_0
import Lemma.List.GetPermute.eq.Get.of.Gt
import Lemma.Int.EqToNat.of.Ge_0
import Lemma.List.Permute.of.Add.ge.SubLength_1
import Lemma.List.GetPermute.eq.Ite.of.GtLength.GtLength
open List


@[main]
private lemma main
  {s : List α}
  {i : Fin s.length}
  {d : ℤ}
  {j : ℕ}
-- given
  (h : i + d > j)
  (h : i > j):
-- imply
  (s.permute i d)[j]'(by simp; grind) = s[j] := by
-- proof
  if h_d : d ≥ 0 then
    rw [← Int.EqToNat.of.Ge_0 h_d]
    rw [List.GetPermute.eq.Get.of.Gt h]
  else
    have h_d := Int.EqNegToNatNeg.of.Lt_0 (by linarith [h_d])
    rw [← h_d]
    rw [List.GetPermute__Neg.eq.Ite.of.GtLength]
    repeat grind

-- created on 2026-07-04
