import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten.of.Lt
import Lemma.Tensor.GetUnflattenDataStack.eq.Data
import Lemma.Tensor.GetCast.eq.Get.of.Eq.Lt
open Tensor Vector


@[main]
private lemma fin.fin
-- given
  (f : Fin n → Tensor α s)
  (i : Fin n) :
-- imply
  ([i < n] f i).get i = f i := by
-- proof
  simp [Tensor.get]
  simp [GetElem.getElem]
  unfold Tensor.toVector
  simp
  have h_i : i < ((n :: s).take 1).prod := by
    simp_all
  have h_n : ((n :: s).take 1).prod = (n :: s).headD 1 := by
    simp_all
  have := GetCast.eq.Get.of.Eq.Lt.fin h_i h_n ((([i < n] f i).data.splitAt 1).map (fun data ↦   ⟨data⟩))
  simp at this
  rw [this]
  apply Eq.of.EqDataS
  simp
  have := GetUnflattenDataStack.eq.Data.fin f i
  simp [GetElem.getElem] at this
  rwa [GetSplitAt_1.eq.GetUnflatten.of.Lt.fin]


@[main]
private lemma fin
-- given
  (f : ℕ → Tensor α s)
  (i : Fin n) :
-- imply
  ([i < n] f i).get i = f i := by
-- proof
  apply fin.fin


@[main]
private lemma main
-- given
  (f : ℕ → Tensor α s)
  (i : Fin n) :
-- imply
  ([i < n] f i)[i] = f i :=
-- proof
  fin f i


@[main]
private lemma fn
-- given
  (f : Fin n → Tensor α s)
  (i : Fin n) :
-- imply
  ([i < n] f i)[i] = f i :=
-- proof
  fin.fin f i


-- created on 2025-05-23
-- updated on 2025-07-17
