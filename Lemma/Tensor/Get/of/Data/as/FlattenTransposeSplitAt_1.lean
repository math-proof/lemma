import sympy.tensor.tensor
import Lemma.Bool.EqCastS.of.SEq.Eq
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetCast_Map.eq.UFnGet.of.Eq.Lt
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.Get
import Lemma.Vector.EqFlattenUnflatten
import Lemma.Vector.Get.of.Flatten.Lt.Lt.Eq.Eq
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten
import Lemma.Vector.Get.of.Eq_FlattenTransposeSplitAt_1
import Lemma.Vector.GetVal.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Vector Tensor Bool
set_option maxHeartbeats 400000


@[main]
private lemma main
-- given
  (X : Tensor α [m, n])
  (X' : Tensor α [n, m])
  (i : Fin m)
  (j : Fin n)
  (h : X'.data ≃ (X.data.splitAt 1).transpose.flatten) :
-- imply
  X'[j, i] = X[i, j] := by
-- proof
  let ⟨v⟩ := X
  let ⟨v'⟩ := X'
  simp at h
  have h := Get.of.Eq_FlattenTransposeSplitAt_1 h i j
  simp [GetElem.getElem]
  unfold Tensor.get
  unfold Tensor.toVector
  simp [GetElem.getElem]
  repeat erw [GetCast_Map.eq.UFnGet.of.Eq.Lt.fin (by simp_all) (by simp_all)]
  apply Eq.of.EqDataS
  simp
  apply EqCastS.of.SEq.Eq (by simp)
  repeat erw [GetSplitAt_1.eq.GetUnflatten.fin]
  repeat erw [Vector.GetVal.eq.Get.fin]
  repeat erw [GetSplitAt_1.eq.GetUnflatten.fin]
  apply SEq.of.All_EqGetS.Eq.fin (by simp)
  intro t
  repeat erw [GetUnflatten.eq.Get_AddMul.fin]
  repeat erw [Get]
  fin_cases t
  simpa [GetElem.getElem]


-- created on 2025-07-18
