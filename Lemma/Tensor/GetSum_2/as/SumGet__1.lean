import Lemma.Tensor.GetSum.as.SumGet.of.Lt_Get_0.Gt_0.GtLength
open Tensor


@[main]
private lemma main
  [Add α] [Zero α]
-- given
  (X : Tensor α [m, n, l])
  (i : Fin m) :
-- imply
  (X.sum 2)[i] ≃ X[i].sum 1 := by
-- proof
  have h_i := i.isLt
  have := GetSum.as.SumGet.of.Lt_Get_0.Gt_0.GtLength (d := 2) (s := [m, n, l]) (by simp) (by simp) h_i X
  simp_all


-- created on 2025-07-12
