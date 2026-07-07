import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.Prod.eq.Foldr
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Fin.Eq_Fin.of.EqVal
import Lemma.Tensor.DataGet.eq.GetUnflattenData
import Lemma.Tensor.Setoid.is.SetoidDataS
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.Setoid.is.All_SetoidGetS
open Fin List Nat Tensor Vector


@[main, comm, mp, mpr, fin, fin.comm, fin.mp, fin.mpr]
private lemma main
  [Setoid α]
-- given
  (A B : Tensor α (m :: s)) :
-- imply
  A ≈ B ↔ ∀ i : Fin m, A[i] ≈ B[i] := by
-- proof
  conv_rhs =>
    simp [Setoid.is.SetoidDataS]
    simp [GetElem.getElem]
    simp [DataGet.eq.GetUnflattenData.fin]
    simp [Setoid.is.All_SetoidGetS.fin]
    simp [GetUnflatten.eq.Get_AddMul.fin]
    simp [Foldr.eq.Prod]
  simp [Setoid.is.SetoidDataS]
  simp [Setoid.is.All_SetoidGetS.fin]
  repeat simp_rw [Tensor.DataGet.eq.GetUnflattenData.fin]
  constructor <;>
    intro h
  ·
    intro t j
    simp [GetElem.getElem]
    repeat erw [Vector.GetUnflatten.eq.Get_AddMul.fin]
    refine h ⟨t * s.prod + j, ?_⟩
  ·
    intro k
    have h_k := k.isLt
    let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_k
    have h_qr := Eq_Fin.of.EqVal h_qr
    simp [h_qr]
    have h := h q r
    simp [GetElem.getElem] at h
    repeat erw [Vector.GetUnflatten.eq.Get_AddMul.fin] at h
    assumption


-- created on 2025-12-24
