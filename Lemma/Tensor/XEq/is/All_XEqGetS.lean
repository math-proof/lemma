import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Fin.Eq_Fin.of.EqVal
import Lemma.Nat.AddMul.lt.Mul
import Lemma.Tensor.DataGet.eq.GetUnflattenData
import Lemma.Tensor.XEq.is.XEqDataS
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.XEq.is.All_XEqGetS
open Fin Nat Tensor Vector


@[main, comm, mp, mpr, fin, fin.comm, fin.mp, fin.mpr]
private lemma main
  [XEq α]
-- given
  (A B : Tensor α (m :: s)) :
-- imply
  A ≈ B ↔ ∀ i : Fin m, A[i] ≈ B[i] := by
-- proof
  rw [XEq.is.XEqDataS]
  rw [Vector.XEq.is.All_XEqGetS.fin]
  constructor
  ·
    intro h i
    rw [XEq.is.XEqDataS]
    simp [GetElem.getElem]
    erw [DataGet.eq.GetUnflattenData.fin]
    erw [DataGet.eq.GetUnflattenData.fin]
    apply Vector.XEq.of.All_XEqGetS.fin
    intro j
    erw [GetUnflatten.eq.Get_AddMul.fin]
    erw [GetUnflatten.eq.Get_AddMul.fin]
    apply h ⟨i * s.prod + j, by simp; apply AddMul.lt.Mul⟩
  ·
    intro h k
    have h_k := k.isLt
    simp at h_k
    let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_k
    have h_qr := Eq_Fin.of.EqVal h_qr
    simp [h_qr]
    have h := h q
    rw [XEq.is.XEqDataS] at h
    simp [GetElem.getElem] at h
    erw [DataGet.eq.GetUnflattenData.fin] at h
    erw [DataGet.eq.GetUnflattenData.fin] at h
    have h := Vector.All_XEqGetS.of.XEq.fin h r
    erw [GetUnflatten.eq.Get_AddMul.fin] at h
    erw [GetUnflatten.eq.Get_AddMul.fin] at h
    assumption


-- created on 2025-12-24
-- updated on 2026-08-27
