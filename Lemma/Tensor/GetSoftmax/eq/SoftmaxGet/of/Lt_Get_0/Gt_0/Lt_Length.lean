import sympy.tensor.functions
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.GetDiv.eq.DivGetS
import Lemma.Tensor.GetExp.eq.ExpGet
import Lemma.Tensor.LengthExp.eq.Length
import Lemma.Bool.EqUFnS.of.Eq
import Lemma.Tensor.GetKeepdim.eq.KeepdimCast_Get.of.Lt_Get_0.Gt_0.Lt_Length
import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.GetSum.as.SumGet.of.Lt_Get_0.Gt_0.Lt_Length
open Tensor Bool


@[main]
private lemma main
  [Exp α]
  {dim i : ℕ}
-- given
  (h_s : dim < s.length)
  (h_d : dim > 0)
  (h_i : i < s[0])
  (X : Tensor α s) :
-- imply
  have : i < (X.softmax dim).length := by rwa [Length.eq.Get_0.of.GtLength_0]
  have : i < X.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  (X.softmax dim)[i] = X[i].softmax (dim - 1) := by
-- proof
  intro h_i' h_iX
  unfold Tensor.softmax
  simp [GetElem.getElem]
  rw [GetDiv.eq.DivGetS.fin (i := ⟨i, by simpa [LengthExp.eq.Length]⟩)]
  rw [GetExp.eq.ExpGet.fin (i := ⟨i, h_iX⟩)]
  apply EqUFnS.of.Eq _ (exp (X.get ⟨i, h_iX⟩) / ·)
  rw [GetKeepdim.eq.KeepdimCast_Get.of.Lt_Get_0.Gt_0.Lt_Length h_s h_d h_i]
  congr
  apply EqCast.of.SEq
  have := GetSum.as.SumGet.of.Lt_Get_0.Gt_0.Lt_Length.fin h_s h_d h_i (exp X)
  apply SEq.trans this
  rw [GetExp.eq.ExpGet.fin (i := ⟨i, h_iX⟩)]


-- created on 2025-10-08
-- updated on 2025-10-11
