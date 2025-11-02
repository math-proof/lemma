import stdlib.SEq
import sympy.tensor.tensor
import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.Tensor.DataGet.eq.GetUnflattenData
import Lemma.Tensor.Lt_Length.of.GtLength_0
import Lemma.Tensor.Lt_LengthSplitAtData.of.GtLength_0
import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten
open Tensor List Vector


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s.length > 0)
  (X : Tensor α s)
  (i : Fin s[0]) :
-- imply
  have := Lt_Length.of.GtLength_0 h X i
  have := Lt_LengthSplitAtData.of.GtLength_0 h X i
  X[i].data ≃ (X.data.splitAt 1)[i] := by
-- proof
  simp
  match s with
  | [] =>
    contradiction
  | n :: s =>
    simp [GetElem.getElem]
    rw [GetSplitAt_1.eq.GetUnflatten.fin]
    rw [DataGet.eq.GetUnflattenData.fin]


@[main]
private lemma fin
  {s : List ℕ}
-- given
  (h : s.length > 0)
  (X : Tensor α s)
  (i : Fin s[0]) :
-- imply
  (X.get ⟨i, Lt_Length.of.GtLength_0 h X i⟩).data ≃ (X.data.splitAt 1).get ⟨i, Lt_LengthSplitAtData.of.GtLength_0 h X i⟩ :=
-- proof
  main h X i


-- created on 2025-11-01
