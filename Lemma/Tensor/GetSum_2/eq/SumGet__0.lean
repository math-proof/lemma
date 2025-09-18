import Lemma.Tensor.GetSum.as.SumGet.of.Lt_Get_0.Gt_0.Lt_Length
import Lemma.Tensor.EqGetS.of.Eq.Lt_Length
import Lemma.Tensor.GetSum_2.as.SumGet__1
import Lemma.Algebra.LtVal
import Lemma.Logic.Eq.of.SEq
open Tensor Algebra Logic


@[main]
private lemma main
  [Add α] [Zero α]
-- given
  (X : Tensor α [m, n, l])
  (i : Fin m)
  (j : Fin n) :
-- imply
  (X.sum 2)[i][j] = X[i][j].sum 0 := by
-- proof
  have h_j := LtVal j
  have h_Xi := GetSum_2.as.SumGet__1 X i
  have h_Xij := EqGetS.of.Eq.Lt_Length h_j h_Xi
  have h_Xij' := GetSum.as.SumGet.of.Lt_Get_0.Gt_0.Lt_Length (dim := 1) (s := [m, n, l].tail) (by simp) (by simp) h_j X[i]
  have h_eq := h_Xij.trans h_Xij'
  apply Eq.of.SEq.simp h_eq


-- created on 2025-07-12
