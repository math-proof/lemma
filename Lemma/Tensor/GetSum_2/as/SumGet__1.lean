import Lemma.Tensor.GetSum.as.SumGet.of.Lt_Get_0.Gt_0.Lt_Length
import Lemma.Algebra.LtVal
open Tensor Algebra


@[main]
private lemma main
  [Add α] [Zero α]
-- given
  (X : Tensor α [m, n, l])
  (i : Fin m) :
-- imply
  (X.sum 2)[i] ≃ X[i].sum 1 := by
-- proof
  have h_i := LtVal i
  have := GetSum.as.SumGet.of.Lt_Get_0.Gt_0.Lt_Length (dim := 2) (s := [m, n, l]) (by simp) (by simp) h_i X
  simp at this
  assumption


-- created on 2025-07-12
