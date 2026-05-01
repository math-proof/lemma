import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.Cons_Append.eq.AppendCons
import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.List.GetAppend.eq.Get.of.GtLength
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdCons.eq.Mul_Prod
import Lemma.List.TailAppend.eq.AppendTail.of.GtLength_0
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.DivDiv.eq.Div_Mul
import Lemma.Nat.DivMod_Mul.eq.ModDiv
import Lemma.Nat.EqAddMulDiv
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.Eq_Fin.of.EqVal
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Tensor.DataAppend.eq.Cast_FlattenMap₂_CastS_SplitAtData
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.DataFromVector.eq.FlattenMapData
import Lemma.Tensor.DataGet.eq.Cast_GetSplitAtData.of.GtLength_0
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Eq.Eq
import Lemma.Tensor.GetToVector.eq.Get.of.GtLength_0
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetAppend.eq.Get.of.Lt
import Lemma.Vector.GetAppend.eq.Get_Sub.of.Lt_Add.Ge
import Lemma.Vector.GetCast.eq.Cast_Get.of.Eq.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Fin List Nat Tensor Vector


@[main]
private lemma main
  {b_z : List ℕ}
-- given
  (h : b_z.length > 0)
  (A : Tensor α (b_z ++ m :: s))
  (B : Tensor α (b_z ++ n :: s)) :
-- imply
  have h_tail : ∀ k, (b_z ++ k :: s).tail = b_z.tail ++ k :: s := by
    intro k
    rw [TailAppend.eq.AppendTail.of.GtLength_0 (by simpa)]
  have h_head : ∀ k, (b_z ++ k :: s).headD 1 = b_z[0] := by
    intro k
    rw [HeadD.eq.Get_0.of.GtLength_0 (by simp)]
    rw [GetAppend.eq.Get.of.GtLength (by simpa)]
  let A' : List.Vector (Tensor α (b_z.tail ++ m :: s)) b_z[0] := cast (by grind) A.toVector
  let B' : List.Vector (Tensor α (b_z.tail ++ n :: s)) b_z[0] := cast (by grind) B.toVector
  A ++ B ≃ Tensor.fromVector (List.Vector.map₂ HAppend.hAppend A' B') := by
-- proof
  intro h_tail h_head A' B'
  simp [A', B']
  apply SEq.of.SEqDataS.Eq
  ·
    rw [Cons_Append.eq.AppendCons]
    rw [EqCons_Tail.of.GtLength_0]
  ·
    rw [DataAppend.eq.Cast_FlattenMap₂_CastS_SplitAtData]
    apply SEq.of.All_EqGetS.Eq.fin
    ·
      intro i
      rw [GetCast.eq.Get.of.Eq.fin]
      ·
        simp
        rw [DataFromVector.eq.FlattenMapData]
        have h_i := i.isLt
        simp only [ProdAppend.eq.MulProdS] at h_i
        rw [ProdCons.eq.Mul_Prod] at h_i
        rw [MulAdd.eq.AddMulS] at h_i
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_i
        let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
        simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
        have h_i : i < b_z[0] * (b_z.tail ++ (m + n) :: s).prod := by
          rw [Mul_Prod.eq.ProdCons]
          rw [Cons_Append.eq.AppendCons]
          rw [EqCons_Tail.of.GtLength_0]
          grind
        let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_i
        let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
        simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
        rw [DataAppend.eq.Cast_FlattenMap₂_CastS_SplitAtData]
        rw [GetCast.eq.Get.of.Eq.fin (by grind)]
        have h_r' := r'.isLt
        simp only [ProdAppend.eq.MulProdS] at h_r'
        rw [ProdCons.eq.Mul_Prod] at h_r'
        rw [MulAdd.eq.AddMulS] at h_r'
        let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_r'
        let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
        simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
        repeat rw [GetCast.eq.Cast_Get.of.Eq.Eq.fin (h_n := by simp) (by simp)]
        repeat rw [GetCast.eq.Cast_Get.of.Eq.Eq.fin (h_s := by grind) (by grind)]
        simp [h_r'_mod] at h_rₐ_mod
        simp [MulAdd.eq.AddMulS] at h_rₐ_mod
        simp [← h_r_mod] at h_rₐ_mod
        have h_rₐ_mod := Eq_Fin.of.EqVal h_rₐ_mod
        simp [h_rₐ_mod]
        have h_eq_q : ↑q = ↑q' * b_z.tail.prod + ↑qₐ := by
          simp [h_q'_div, h_qₐ_div, h_q_div, h_r'_mod]
          rw [AddMulS.eq.MulAdd]
          rw [DivMod_Mul.eq.ModDiv.comm]
          rw [Div_Mul.eq.DivDiv.comm (c := b_z.tail.prod)]
          rw [EqAddMulDiv]
        by_cases h_r : r < m * s.prod <;>
        ·
          repeat rw [GetAppend.eq.Get.of.Lt.fin (by grind)]
          repeat rw [GetAppend.eq.Get_Sub.of.Lt_Add.Ge.fin (by omega)]
          repeat rw [GetCast.eq.Get.of.Eq.fin (by grind)]
          simp
          repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          simp
          rw [DataCast.eq.Cast_Data.of.Eq (by grind)]
          rw [GetCast.eq.Get.of.Eq.fin (by grind)]
          rw [GetToVector.eq.Get.of.GtLength_0 (by grind) (i := ⟨q', by rw [GetAppend.eq.Get.of.GtLength (by grind)]; grind⟩)]
          rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (by grind) (i := ⟨q', by grind⟩)]
          rw [GetCast.eq.Get.of.Eq.fin (by simp)]
          rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          simp
          apply congrArg
          simp [Add_Add.eq.AddAdd]
          rw [TailAppend.eq.AppendTail.of.GtLength_0 (by simpa)]
          rw [ProdAppend.eq.MulProdS]
          conv_rhs => rw [Mul_Mul.eq.MulMul]
          rw [ProdCons.eq.Mul_Prod]
          simp [AddMulS.eq.MulAdd, h_eq_q]
      ·
        grind
    ·
      apply congrArg
      rw [Cons_Append.eq.AppendCons]
      rw [EqCons_Tail.of.GtLength_0]


-- created on 2026-04-25
-- updated on 2026-05-01
