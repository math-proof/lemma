import Lemma.Vector.Sum.eq.Sum_Get
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.DataSum.eq.Sum_Data
import Lemma.Fin.HEq.of.All_Eq.Eq
import Lemma.Vector.GetCast_Map.eq.UFnGet.of.Eq.Lt
open Tensor Vector Fin


@[main, fin]
private lemma main
  [AddCommMonoid α]
-- given
  (X : Tensor α (n :: s)) :
-- imply
  X.sum 0 = ∑ i : Fin n, X[i] := by
-- proof
  unfold Tensor.sum
  apply Eq.of.EqDataS
  simp [Sum.eq.Sum_Get]
  rw [DataSum.eq.Sum_Data (A := fun i : Fin n => X[i.val])]
  congr
  repeat simp
  apply HEq.of.All_Eq.Eq (by simp)
  intro i
  simp [GetElem.getElem]
  unfold Tensor.get Tensor.toVector
  have := i.isLt
  simp
  rw [GetCast_Map.eq.UFnGet.of.Eq.Lt (by simp_all) (by simp)]
  simp [GetElem.getElem]


-- created on 2025-07-13
-- updated on 2025-07-15
