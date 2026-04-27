import Lemma.Tensor.GetCast.eq.Cast_Get.of.Eq.Eq
import Lemma.Vector.GetCast.eq.Cast_Get.of.Eq.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.Cons_Append.eq.AppendCons
import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.List.GetAppend.eq.Get.of.GtLength
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdCons.eq.Mul_Prod
import Lemma.List.TailAppend.eq.AppendTail.of.GtLength_0
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Tensor.DataAppend.eq.Cast_FlattenMap₂_CastS_SplitAtData
import Lemma.Tensor.DataFromVector.eq.FlattenMapData
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
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
        simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
        have h_i : i < b_z[0] * (b_z.tail ++ (m + n) :: s).prod := by
          rw [List.Mul_Prod.eq.ProdCons]
          rw [Cons_Append.eq.AppendCons]
          rw [EqCons_Tail.of.GtLength_0]
          grind
        let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_i
        simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
        rw [DataAppend.eq.Cast_FlattenMap₂_CastS_SplitAtData]
        rw [GetCast.eq.Get.of.Eq.fin (by grind)]
        have h_r' := r'.isLt
        simp only [ProdAppend.eq.MulProdS] at h_r'
        rw [ProdCons.eq.Mul_Prod] at h_r'
        rw [MulAdd.eq.AddMulS] at h_r'
        let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_r'
        simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
        -- unfold List.Vector.splitAt
        repeat rw [Vector.GetCast.eq.Cast_Get.of.Eq.Eq.fin (by simp) (by simp)]
        repeat rw [Tensor.GetCast.eq.Cast_Get.of.Eq.Eq.fin (by grind) (by grind)]
        sorry
      ·
        grind
    ·
      apply congrArg
      rw [Cons_Append.eq.AppendCons]
      rw [EqCons_Tail.of.GtLength_0]


-- created on 2026-04-25
