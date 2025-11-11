import sympy.tensor.tensor
import Lemma.Vector.GetCast_Map.eq.UFnGet.of.Eq.Lt
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.EqGetS
import Lemma.Vector.EqFlattenUnflatten
import Lemma.Vector.EqGetS.of.EqFlattenS.Lt.Lt.Eq.Eq
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten
import Lemma.Vector.EqGetS.of.Eq_FlattenTransposeSplitAt_1
open Vector


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
  have h := EqGetS.of.Eq_FlattenTransposeSplitAt_1 h i j
  simp [GetElem.getElem]
  unfold Tensor.get
  unfold Tensor.toVector
  simp [GetElem.getElem]
  repeat rw [GetCast_Map.eq.UFnGet.of.Eq.Lt.fin]
  ·
    simp
    repeat rw [GetSplitAt_1.eq.GetUnflatten.fin]
    simp
    apply Eq.of.All_EqGetS
    intro t
    simp only [GetElem.getElem]
    repeat rw [GetUnflatten.eq.Get_AddMul.fin]
    simpa [EqGetS]
  repeat simp


-- created on 2025-07-18
