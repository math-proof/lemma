import Lemma.Fin.HEq.of.All_Eq.Eq
import Lemma.Tensor.DataSum.eq.Sum_Data
import Lemma.Tensor.DataSum_0.eq.SumSplitAtData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetCast_Map.eq.UFnGet.of.Eq.Lt
import Lemma.Vector.Sum.eq.Sum_Get
open Fin Tensor Vector


@[main, fin]
private lemma main
  [AddCommMonoid α]
-- given
  (X : Tensor α (n :: s)) :
-- imply
  X.sum 0 = ∑ i : Fin n, X[i] := by
-- proof
  apply Eq.of.EqDataS
  rw [DataSum_0.eq.SumSplitAtData]
  simp [GetElem.getElem]
  apply Eq.trans (Sum.eq.Sum_Get (X.data.splitAt 1))
  apply Eq.trans _ (DataSum.eq.Sum_Data Finset.univ (A := fun i : Fin n => X[i])).symm
  congr
  repeat simp
  apply HEq.of.All_Eq.Eq (by simp)
  intro i
  simp [GetElem.getElem, Tensor.get, Tensor.toVector]
  rw [GetCast_Map.eq.UFnGet.of.Eq.Lt.fin (by exact i.isLt) (by simp)]


-- created on 2025-07-13
-- updated on 2026-07-22
