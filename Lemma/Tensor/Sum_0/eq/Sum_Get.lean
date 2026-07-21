import Lemma.Vector.GetCast_Map.eq.UFnGet.of.Eq.Lt
import Lemma.Vector.Sum.eq.Sum_Get
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.DataSum.eq.Sum_Data
import Lemma.Fin.HEq.of.All_Eq.Eq
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
  simp
  have h_data : ((∑ i : Fin n, X.get i) : Tensor α s).data = ∑ i : Fin n, (X.get i).data := by
    dsimp [GetElem.getElem]
    simpa [List.tail_cons] using! DataSum.eq.Sum_Data Finset.univ (A := fun i : Fin n => X[i])
  apply Eq.trans (Sum.eq.Sum_Get (X.data.splitAt 1))
  apply Eq.trans _ h_data.symm
  congr
  repeat simp
  apply HEq.of.All_Eq.Eq (by simp)
  intro i
  simp [GetElem.getElem, Tensor.get, Tensor.toVector]
  rw [GetCast_Map.eq.UFnGet.of.Eq.Lt.fin (by exact i.isLt) (by simp)]


-- created on 2025-07-13
-- updated on 2025-07-15
