import Lemma.Bool.EqCast.of.SEq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Fin.Eq_Fin.of.EqVal
import Lemma.List.DropDrop.eq.Drop_Add
import Lemma.List.Prod.eq.MulProdS
import Lemma.List.ProdEraseIdx.eq.MulProdS
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.Div.eq.AddMulDiv_Mul
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Tensor.DataFromVector.eq.FlattenMapData
import Lemma.Tensor.DataGet.eq.GetUnflattenData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetSum.eq.SumMapGet
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool Fin List Nat Tensor Vector


@[main]
private lemma main
  [Add α] [Zero α]
-- given
  (X : Tensor α (n :: s))
  (d : ℕ) :
-- imply
  X.sum (d + 1) = Tensor.fromVector (X.toVector.map (·.sum d)) := by
-- proof
  unfold Tensor.sum
  apply Eq.of.EqDataS
  simp
  apply EqCast.of.SEq
  rw [DataFromVector.eq.FlattenMapData]
  simp
  apply SEq.of.All_EqGetS.Eq.fin
  ·
    intro t
    have h_t := t.isLt
    let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
    let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
    rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
    simp
    simp at h_t
    simp only [MulMul.eq.Mul_Mul] at h_t
    rw [MulProdS.eq.ProdEraseIdx] at h_t
    let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
    let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
    rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
    simp
    rw [GetCast.eq.Get.of.Eq.fin (by simp; grind)]
    have h_r' := r'.isLt
    simp only [ProdEraseIdx.eq.MulProdS] at h_r'
    simp only [Drop_Add.eq.DropDrop] at h_r'
    let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_r'
    let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
    rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
    simp
    erw [GetSum.eq.SumMapGet.fin]
    erw [GetSum.eq.SumMapGet.fin]
    congr 1
    simp [h_r'_mod] at h_rₐ_mod
    simp at h_r_mod
    simp [ProdEraseIdx.eq.MulProdS] at h_rₐ_mod
    have h_rₐ := h_rₐ_mod.trans h_r_mod.symm
    have h_rₐ := Eq_Fin.of.EqVal h_rₐ
    simp [h_rₐ]
    congr 1
    congr 1
    erw [GetToVector.eq.Get.fin]
    ext j
    rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
    erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
    simp
    rw [DataGet.eq.GetUnflattenData.fin]
    erw [GetUnflatten.eq.Get_AddMul.fin]
    simp
    congr 1
    simp
    rw [Add_Add.eq.AddAdd]
    congr 1
    rw [Prod.eq.MulProdS s d]
    rw [Mul_Mul.eq.MulMul]
    rw [AddMulS.eq.MulAdd]
    congr 1
    simp only [h_q'_div, h_qₐ_div, h_q_div, h_r'_mod]
    simp [ProdEraseIdx.eq.MulProdS]
    apply Div.eq.AddMulDiv_Mul
  ·
    rw [MulMul.eq.Mul_Mul]
    congr 1
    simp
    grind


-- created on 2025-06-27
-- updated on 2026-07-22
