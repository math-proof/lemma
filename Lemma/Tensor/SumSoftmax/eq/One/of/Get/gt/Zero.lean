import sympy.tensor.functions
import Lemma.Tensor.Softmax.eq.Div_SumExp
import Lemma.Tensor.Sum.eq.GetEllipsisKeepdimSum.of.Get.gt.Zero
import Lemma.Nat.Gt_0
import Lemma.Tensor.SumSoftmax.eq.One.of.Get_SubLength_1.gt.Zero.GtLength_0
import Lemma.Nat.Eq_Mk.of.EqVal
open Tensor Nat


@[main]
private lemma main
  [ExpPos α] [IsOrderedCancelAddMonoid α]
  {dim : Fin s.length}
-- given
  (h : s[dim] > 0)
  (X : Tensor α s) :
-- imply
  (X.softmax dim).sum dim = 1 := by
-- proof
  by_cases h_dim : dim = s.length - 1
  ·
    have h_pos := Gt_0 dim
    have h_dim : dim = ⟨s.length - 1, by simp [h_pos]⟩ := Eq_Mk.of.EqVal h_dim
    subst h_dim
    simp
    apply SumSoftmax.eq.One.of.Get_SubLength_1.gt.Zero.GtLength_0 h_pos h
  ·
    rw [Softmax.eq.Div_SumExp]
    rw [Sum.eq.GetEllipsisKeepdimSum.of.Get.gt.Zero h]
    sorry


-- created on 2025-10-03
-- updated on 2025-10-12
