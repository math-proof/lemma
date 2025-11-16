import Lemma.Vector.Sum.eq.Sum_Get
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.DataSum.eq.Sum_Data
import Lemma.Bool.HEq.of.All_Eq.Eq
import Lemma.Vector.GetCast_Map.eq.UFnGet.of.Eq.Lt
open Tensor Vector Bool


@[main]
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
  apply HEq.of.All_Eq.Eq.fin (by simp)
  intro i
  simp [GetElem.getElem]
  obtain ⟨data⟩ := X
  unfold Tensor.get Tensor.toVector
  have := i.isLt
  simp
  rw [GetCast_Map.eq.UFnGet.of.Eq.Lt (by simp_all) (by simp)]
  simp [GetElem.getElem]


@[main]
private lemma fin
  [AddCommMonoid α]
-- given
  (X : Tensor α (n :: s)) :
-- imply
  X.sum 0 = ∑ i : Fin n, X.get i := by
-- proof
  apply main


-- created on 2025-07-13
-- updated on 2025-07-15
