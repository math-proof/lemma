import Lemma.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
import Lemma.Int.Add_ToNatNeg.eq.ToNatSub.of.Le_0
import Lemma.Algebra.EqMax.of.Ge
import Lemma.Algebra.GeNeg_0.of.Le_0
open Algebra List Int


@[main]
private lemma main
  {s : List α}
  {d : Fin s.length}
  {k : ℤ}
-- given
  (h_k : k ≤ 0)
  (h : d.val = s.length - 1) :
-- imply
  s.permute d k = s.take (s.length - (1 - k).toNat) ++ (s.drop (s.length - (1 - k).toNat)).rotate ((1 - k).toNat ⊓ s.length - 1) := by
-- proof
  have := Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 h (-k).toNat
  rw [Add_ToNatNeg.eq.ToNatSub.of.Le_0 h_k] at this
  simp [EqMax.of.Ge (GeNeg_0.of.Le_0 h_k)] at this
  simp [← this]


-- created on 2025-07-14
