import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.EqGetS
import Lemma.Vector.EqFlattenUnflatten
import Lemma.Vector.EqGetS.of.EqFlattenS.Lt.Lt.Eq.Eq
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten
import Lemma.Nat.AddMul.lt.Mul
open Vector Nat


@[main]
private lemma main
  {v : List.Vector α [m, n].prod}
  {v' : List.Vector α [n, m].prod}
-- given
  (h : v' ≃ (v.splitAt 1).transpose.flatten)
  (i : Fin m)
  (j : Fin n):
-- imply
  have : j * m + i < [n, m].prod := by simp [AddMul.lt.Mul j i]
  have : i * n + j < [m, n].prod := by simp [AddMul.lt.Mul i j]
  v'[j * m + i] = v[i * n + j] := by
-- proof
  rw [← EqFlattenUnflatten v'] at h
  have h_get := EqGetS.of.EqFlattenS.Lt.Lt.Eq.Eq
    (n := m * 1) (m := n * 1) (n' := [m].prod) (m' := n) (i := j) (j := i)
    (by simp) (by simp) (by simp) (by simp) h
  simp [GetElem.getElem] at h_get
  rw [GetTranspose.eq.Get.fin] at h_get
  rw [GetSplitAt_1.eq.GetUnflatten.fin] at h_get
  repeat rw [GetUnflatten.eq.Get_AddMul.fin] at h_get
  simp [EqGetS] at h_get
  assumption


-- created on 2025-07-18
