import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Tensor.GetData.eq.GetDataGet.of.GtProd.GtLength_0
open Tensor


@[main, fin]
private lemma main
-- given
  (h_i : i < n)
  (X : Tensor α [n]) :
-- imply
  have := GtLength.of.GtLength_0 (by grind) X ⟨i, by grind⟩
  X.data[i]'(by simpa) = X[i].data[0] := by
-- proof
  have := GetData.eq.GetDataGet.of.GtProd.GtLength_0 (by simp) (by simpa) X (i := i)
  grind


-- created on 2025-10-11
