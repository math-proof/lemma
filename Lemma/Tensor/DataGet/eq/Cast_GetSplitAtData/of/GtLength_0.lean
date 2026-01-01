import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Tensor.Lt_LengthSplitAtData.of.GtLength_0
import Lemma.Tensor.DataGet.as.GetSplitAtData.of.GtLength_0
import sympy.tensor.tensor
open Tensor Bool


@[main, fin]
private lemma main
  {s : List ℕ}
-- given
  (h : s.length > 0)
  (X : Tensor α s)
  (i : Fin s[0]) :
-- imply
  have := GtLength.of.GtLength_0 h X i
  have := Lt_LengthSplitAtData.of.GtLength_0 h X i
  X[i].data = cast (by simp) (X.data.splitAt 1)[i] := by
-- proof
  apply Eq_Cast.of.SEq
  apply DataGet.as.GetSplitAtData.of.GtLength_0 h


-- created on 2025-11-02
