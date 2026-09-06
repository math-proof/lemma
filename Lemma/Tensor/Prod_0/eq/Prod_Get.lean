import Lemma.Fin.HEq.of.All_Eq.Eq
import Lemma.Tensor.DataProd.eq.Prod_Data
import Lemma.Tensor.DataProd_0.eq.ProdSplitAtData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetCast_Map.eq.UFnGet.of.Eq.Lt
import Lemma.Vector.Prod.eq.Prod_Get
open Fin Tensor Vector


@[main, fin, comm, fin.comm]
private lemma main
  [CommMonoid α]
-- given
  (X : Tensor α (n :: s)) :
-- imply
  X.prod 0 = ∏ i : Fin n, X[i] := by
-- proof
  apply Eq.of.EqDataS
  rw [DataProd_0.eq.ProdSplitAtData]
  simp [GetElem.getElem]
  apply Eq.trans (Prod.eq.Prod_Get (X.data.splitAt 1))
  apply Eq.trans _ (DataProd.eq.Prod_Data Finset.univ (A := fun i : Fin n => X[i])).symm
  congr
  repeat simp
  apply HEq.of.All_Eq.Eq (by simp)
  intro i
  simp [GetElem.getElem, Tensor.get, Tensor.toVector]
  erw [GetCast_Map.eq.UFnGet.of.Eq.Lt.fin (by exact i.isLt) (by simp)]
  rfl


-- created on 2026-09-06
