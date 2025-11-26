import Lemma.Tensor.LengthRepeat.eq.Get_0.of.GtVal_0
import Lemma.Nat.LtSubS.of.Lt.Le
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.List.TailSet.eq.SetTail.of.Gt_0
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.List.GetSet.eq.Get.of.Ne.GtLength
import Lemma.Nat.Gt_0
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Vector.GetMap.eq.UFnGet.of.Lt
import Lemma.Nat.Ge_1.of.Gt_0
import Lemma.Nat.Gt_0.of.Gt
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.Nat.MulMul
import Lemma.Vector.GetCast_Map.eq.UFnGet.of.Eq.Lt
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Nat.Mul_Mul
import Lemma.List.MulProd_Mul_Prod.eq.Mul_Prod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop
import Lemma.List.AddMul_ProdSet.lt.MulProd_Mul_Prod.of.Lt_Mul_ProdTail.Lt_Get_0.GtVal_0.GtLength_0
import Lemma.List.ProdTailSet.eq.Mul_ProdTail.LtLength_0.Gt_0
import Lemma.List.ProdSet__Mul_Get.eq.Mul_Prod.of.GtLength
import Lemma.Nat.Any_EqAddMul.of.Lt_Mul
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetRepeat_AddMul.eq.Get.of.Eq_AddMul
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.Mul
import Lemma.Vector.EqGetS
import Lemma.List.ProdTakeSet.eq.Get_0.of.Gt_0.GtLength_0
import Lemma.List.GetSet.eq.Get_0.of.Gt_0.GtLength_0
import Lemma.List.HeadDSet.eq.Get_0.of.Gt_0.LtLength
import Lemma.List.ProdTailSet.eq.Mul_ProdTailDrop.LtLength_0.Gt_0
import Lemma.List.ProdTake_1.eq.HeadD_1
import Lemma.Bool.EqUFnS.of.Eq
import Lemma.List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.Vector.EqGetSSplitAt.of.Lt_Mul_ProdTail.Gt_0.Lt_Get_0.GtLength_0
import Lemma.Vector.EqGetS.of.EqFlattenS.Lt.Lt.Eq.Eq
import Lemma.List.Lt_ProdTakeSet.of.Gt_0.Lt_Get_0.GtLength_0
import Lemma.List.Lt_ProdDropSet.of.Lt_Mul_ProdTail.GtVal_0
import Lemma.Tensor.HEq.of.SEqDataS.Eq
import Lemma.Vector.SEqFlattenSSplitAt.of.SEq
import Lemma.Bool.SEqCast.of.Eq
open Tensor Vector List Bool Nat


@[main]
private lemma main
  {d : Fin s.length}
-- given
  (h : d.val > 0)
  (h_i : i < s[0])
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  have : i < (X.repeat n d).length := by simpa [LengthRepeat.eq.Get_0.of.GtVal_0 h]
  have : d - 1 < s.tail.length := by
    simp
    apply LtSubS.of.Lt.Le (by linarith) (by simp)
  have : i < X.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  (X.repeat n d)[i] ≃ X[i].repeat n ⟨d - 1, by assumption⟩ := by
-- proof
  intro h_i' h_d' h_i'
  unfold Tensor.repeat
  constructor
  ·
    rw [← TailSet.eq.SetTail.of.Gt_0 (by assumption)]
    simp
    congr
    rwa [EqAddSub.of.Ge]
  ·
    simp
    simp only [GetElem.getElem]
    simp [Tensor.get]
    simp [Tensor.toVector]
    obtain ⟨data⟩ := X
    have h_s := Gt_0 d
    have h_d := Ge_1.of.Gt_0 h
    simp
    simp only [GetElem.getElem]
    -- /(?<!Lemma\.)(Tensor|Algebra)\.(?![a-z]|T\b)/i
    rw [GetCast.eq.Get.of.Eq.fin (n' := (s.set d (n * s[d.val])).headD 1)]
    ·
      rw [GetMap.eq.UFnGet.of.Lt.fin]
      apply HEq.of.SEqDataS.Eq (by simp_all)
      apply SEqCastS.of.SEq.Eq.Eq
      ·
        simp
      ·
        rw [MulProd_Mul_Prod.eq.Mul_Prod]
        rw [ProdSet__Mul_Get.eq.Mul_Prod.of.GtLength.fin]
      ·
        rw [GetCast_Map.eq.UFnGet.of.Eq.Lt.fin]
        ·
          simp
          apply SEq.of.All_EqGetS.Eq
          ·
            intro t
            have h_t : t < n * s.tail.prod := by
              convert t.isLt
              simp
              rwa [ProdTailSet.eq.Mul_ProdTail.LtLength_0.Gt_0]
            simp only [GetElem.getElem]
            have h_eq := MulProd_Mul_Prod.eq.ProdSet__Mul_Get.of.GtLength (d.isLt) n
            have h_eq := EqUFnS.of.Eq h_eq (List.Vector α)
            have h_i_prod := Lt_ProdTakeSet.of.Gt_0.Lt_Get_0.GtLength_0 (by assumption) h_i h (n * s[d])
            have h_t_prod := Lt_ProdDropSet.of.Lt_Mul_ProdTail.GtVal_0 h h_t
            have := GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop.fin
              h_i_prod h_t_prod
              ((cast h_eq (List.Vector.map (·.repeat n) (data.splitAt d)).flatten))
            simp at this
            simp [this]
            rw [GetCast.eq.Get.of.Eq.fin (n' := (s.set d (n * s[d])).prod)]
            ·
              have h_t' : t < (s.tail.take (d - 1)).prod * (n * (s.tail.drop (d - 1)).prod) := by
                rwa [MulProd_Mul_Prod.eq.Mul_Prod s.tail n (d - 1)]
              obtain ⟨i', j', h_eq⟩ := Any_EqAddMul.of.Lt_Mul h_t'
              obtain ⟨h_i'_eq, h_j'_eq⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_eq.symm
              simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_eq.symm]
              simp [ProdTailSet.eq.Mul_ProdTail.LtLength_0.Gt_0 h]
              have h_it := AddMul.lt.Mul.of.Lt.Lt h_i h_t
              rw [Mul_Mul.eq.MulMul (a := s[0])] at h_it
              rw [MulMul.comm] at h_it
              rw [← Prod.eq.Mul_ProdTail.of.GtLength_0 (by linarith)] at h_it
              rw [Mul.comm (a := s.prod)] at h_it
              rw [← MulProd_Mul_Prod.eq.Mul_Prod s n d] at h_it
              obtain ⟨i'', j'', h_eq⟩ := Any_EqAddMul.of.Lt_Mul h_it
              obtain ⟨h_i''_eq, h_j''_eq⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_eq.symm
              simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_eq.symm]
              have h_j' := j'.isLt
              obtain ⟨j_i', j_j', h_eq⟩ := Any_EqAddMul.of.Lt_Mul h_j'
              obtain ⟨h_j_i'_eq, h_j_j'_eq⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_eq.symm
              simp [GetRepeat_AddMul.eq.Get.of.Eq_AddMul.fin h_eq.symm]
              have h_j'' := j''.isLt
              obtain ⟨j_i'', j_j'', h_eq⟩ := Any_EqAddMul.of.Lt_Mul h_j''
              obtain ⟨h_j_i''_eq, h_j_j''_eq⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_eq.symm
              simp [GetRepeat_AddMul.eq.Get.of.Eq_AddMul.fin h_eq.symm]
              simp [EqGetS]
              simp [h_i''_eq, h_j_j''_eq, h_j''_eq, h_i'_eq, h_j_j'_eq, h_j'_eq]
              simp [EqAddSub.of.Ge h_d]
              rw [EqGetSSplitAt.of.Lt_Mul_ProdTail.Gt_0.Lt_Get_0.GtLength_0 h_s h_i h_d h_t data]
              apply EqGetS.of.EqFlattenS.Lt.Lt.Eq.Eq (by simp) (by simp)
              simp_all
              apply SEqFlattenSSplitAt.of.SEq
              .
                apply SEq_Cast.of.Eq
                simp
              .
                simp_all
            ·
              apply MulProd_Mul_Prod.eq.ProdSet__Mul_Get.of.GtLength
          ·
            simp
            rw [ProdTailSet.eq.Mul_ProdTailDrop.LtLength_0.Gt_0]
            repeat simp_all
        ·
          rw [ProdTake_1.eq.HeadD_1]
      ·
        rw [List.HeadD.eq.Get_0.of.GtLength_0 (by simpa)]
        rw [GetSet.eq.Get_0.of.Gt_0.GtLength_0 h_s h_d]
        rw [List.ProdTake_1.eq.Get_0.of.GtLength_0 (by simpa)]
        simp
        rw [GetSet.eq.Get_0.of.Gt_0.GtLength_0 h_s h_d]


@[main]
private lemma fin
  {d : Fin s.length}
-- given
  (h : d.val > 0)
  (h_i : i < s[0])
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  (X.repeat n d).get ⟨i, by simpa [LengthRepeat.eq.Get_0.of.GtVal_0 h]⟩ ≃ (X.get ⟨i, by rwa [Length.eq.Get_0.of.GtLength_0]⟩).repeat n ⟨d - 1, by
    simp
    apply LtSubS.of.Lt.Le (by linarith) (by simp)⟩ := by
-- proof
  apply main h h_i X n


-- created on 2025-07-05
-- updated on 2025-07-17
