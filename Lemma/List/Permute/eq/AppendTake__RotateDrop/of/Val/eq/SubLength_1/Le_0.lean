import Lemma.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
import Lemma.Int.Add_ToNatNeg.eq.ToNatSub.of.Le_0
import Lemma.Nat.EqMax.of.Ge
import Lemma.Algebra.GeNeg_0.of.Le_0
open Algebra List Int Nat


@[main]
private lemma main
  {s : List α}
  {i : Fin s.length}
  {d : ℤ}
-- given
  (h_d : d ≤ 0)
  (h_i : i.val = s.length - 1) :
-- imply
  s.permute i d = s.take (s.length - (1 - d).toNat) ++ (s.drop (s.length - (1 - d).toNat)).rotate ((1 - d).toNat ⊓ s.length - 1) := by
-- proof
  have := Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 h_i (-d).toNat
  rw [Add_ToNatNeg.eq.ToNatSub.of.Le_0 h_d] at this
  simp [EqMax.of.Ge (GeNeg_0.of.Le_0 h_d)] at this
  simp [← this]


-- created on 2025-07-14
