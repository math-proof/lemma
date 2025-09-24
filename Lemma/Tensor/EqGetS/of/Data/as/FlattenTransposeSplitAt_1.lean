import sympy.tensor.tensor
import Lemma.Algebra.GetCast_Map.eq.UFnGet.of.Eq.Lt
import Lemma.Vector.Eq.of.All_EqGetS
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Algebra.EqGetS
import Lemma.Algebra.EqFlattenUnflatten
import Lemma.Algebra.EqGetS.of.EqFlattenS.Lt.Lt.Eq.Eq
import Lemma.Algebra.GetTranspose.eq.Get
import Lemma.Vector.GetUnflatten.eq.GetSplitAt_1
import Lemma.Algebra.EqGetS.of.Eq_FlattenTransposeSplitAt_1
open Algebra Vector


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
