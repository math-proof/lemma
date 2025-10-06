import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthSum.eq.Length.of.Gt_0
import Lemma.List.Sub_1.lt.LengthTail.of.Gt_0.Lt_Length
import Lemma.List.EraseIdxTail.eq.TailEraseIdx.of.Lt_LengthTail
import Lemma.Algebra.EqAddSub.of.Ge
import Lemma.Tensor.GetSum.as.SumGet.of.Lt_Get_0.Gt_0.Lt_Length
import Lemma.Logic.EqCast.of.SEq
open Tensor Algebra Logic List


@[main]
private lemma main
  [Add α] [Zero α]
  {dim i : ℕ}
-- given
  (h₀ : dim < s.length)
  (h₁ : dim > 0)
  (h₂ : i < s[0])
  (X : Tensor α s) :
-- imply
  have h_shape := LengthSum.eq.Length.of.Gt_0 h₁ X
  have h_i : i < X.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  (X.sum dim)[i] = cast (by
    let h_dim := Sub_1.lt.LengthTail.of.Gt_0.Lt_Length h₀ h₁
    rw [EraseIdxTail.eq.TailEraseIdx.of.Lt_LengthTail h_dim]
    congr
    rw [EqAddSub.of.Ge (by assumption)]
  ) (X[i].sum (dim - 1)) := by
-- proof
  have := GetSum.as.SumGet.of.Lt_Get_0.Gt_0.Lt_Length h₀ h₁ h₂ X
  apply Eq_Cast.of.SEq this


-- created on 2025-06-22
-- updated on 2025-07-13
