import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.Prod.eq.Foldr
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Eq_Fin.of.EqVal
import Lemma.Tensor.DataGet.eq.GetUnflattenData
import Lemma.Tensor.Setoid.is.SetoidDataS
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.Setoid.is.All_SetoidGetS
open Fin List Nat Tensor Vector


@[main, comm, mp, mpr]
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
  constructor <;>
    intro h
  ·
    intro t j
    apply h ⟨t * s.prod + j, by
      apply AddMul.lt.Mul.of.Lt.Lt
      ·
        grind
      ·
        have h_j := j.isLt
        simp [Foldr.eq.Prod] at h_j
        assumption⟩
  ·
    intro k
    have h_k := k.isLt
    let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_k
    have h_qr := Eq_Fin.of.EqVal h_qr
    simp [h_qr]
    apply h q r


-- created on 2025-12-24
