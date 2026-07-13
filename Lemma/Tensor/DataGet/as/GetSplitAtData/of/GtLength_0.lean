import stdlib.SEq
import sympy.tensor.tensor
import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.Tensor.DataGet.eq.GetUnflattenData
import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Tensor.GtLengthSplitAtData.of.GtLength_0
import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten
open Tensor List Vector


@[main, fin, cast, cast.fin]
private lemma main
  {s : List ℕ}
-- given
  (h : s.length > 0)
  (X : Tensor α s)
  (i : Fin s[0]) :
-- imply
  have := GtLength.of.GtLength_0 h X i
  X[i].data ≃ (X.data.splitAt 1)[i]'(GtLengthSplitAtData.of.GtLength_0 h X i) := by
-- proof
  match s with
  | [] =>
    contradiction
  | n :: s =>
    simp [GetElem.getElem]
    erw [GetSplitAt_1.eq.GetUnflatten.fin]
    rw [DataGet.eq.GetUnflattenData.fin]


-- created on 2025-11-01
