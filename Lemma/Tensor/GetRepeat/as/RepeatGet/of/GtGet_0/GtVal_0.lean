import Lemma.Bool.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.GetSet.eq.Get_0.of.Gt_0.GtLength_0
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.List.MulProd_Mul_Prod.eq.Mul_Prod
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.List.ProdSet__Mul_Get.eq.Mul_Prod.of.GtLength
import Lemma.List.ProdTailSet.eq.Mul_ProdTail.LtLength_0.Gt_0
import Lemma.List.ProdTailSet.eq.Mul_ProdTailDrop.LtLength_0.Gt_0
import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.List.ProdTake_1.eq.HeadD_1
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Any_EqAddMul.of.Lt_Mul
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.Ge_1.of.Gt_0
import Lemma.Nat.Gt_0
import Lemma.Nat.Mul
import Lemma.Nat.MulMul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.Mul_Mul
import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Tensor.LengthRepeat.eq.Length.of.GtVal_0
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.Get
import Lemma.Vector.Get.of.Flatten.Lt.Lt.Eq.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetCast_Map.eq.UFnGet.of.Eq.Lt
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetMap.eq.UFnGet.of.Lt
import Lemma.Vector.GetRepeat_AddMul.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop
import Lemma.Vector.GetSplitAt.of.Lt_Mul_ProdTail.Gt_0.GtGet_0.GtLength_0
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.SEqFlattenSSplitAt.of.SEq
import sympy.tensor.tensor
open Bool List Nat Tensor Vector


@[main, fin, cast, cast.fin]
private lemma main
  {d : Fin s.length}
-- given
  (h_d : d.val > 0)
  (h_i : i < s[0])
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  have := GtLength.of.GtLength_0 (by grind) X ⟨i, by grind⟩
  (X.repeat d n)[i]'(by rwa [LengthRepeat.eq.Length.of.GtVal_0 h_d]) ≃ X[i].repeat ⟨d - 1, by grind⟩ n := by
-- proof
  simp
  simp only [GetElem.getElem]
  unfold Tensor.repeat
  simp [Tensor.get]
  simp [Tensor.toVector]
  obtain ⟨X⟩ := X
  have h_s := Gt_0 d
  have h_d := Ge_1.of.Gt_0 h_d
  simp
  simp only [GetElem.getElem]
  rw [GetCast.eq.Get.of.Eq.fin]
  ·
    rw [GetMap.eq.UFnGet.of.Lt.fin]
    apply SEq.of.SEqDataS.Eq (by simp_all)
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
          have h_t := t.isLt
          have h_t : t < n * s.tail.prod := by
            convert h_t
            simp
            rwa [ProdTailSet.eq.Mul_ProdTail.LtLength_0.Gt_0]
          simp only [GetElem.getElem]
          rw [GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop.fin]
          rw [GetCast.eq.Get.of.Eq.fin]
          ·
            have h_t' : t < (s.tail.take (d - 1)).prod * (n * (s.tail.drop (d - 1)).prod) := by
              rwa [MulProd_Mul_Prod.eq.Mul_Prod s.tail n (d - 1)]
            obtain ⟨i', j', h_eq⟩ := Any_EqAddMul.of.Lt_Mul h_t'
            obtain ⟨h_i'_eq, h_j'_eq⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_eq.symm
            rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_eq.symm]
            simp [ProdTailSet.eq.Mul_ProdTail.LtLength_0.Gt_0 h_d]
            have h_it := AddMul.lt.Mul.of.Lt.Lt h_i h_t
            rw [Mul_Mul.eq.MulMul (a := s[0])] at h_it
            rw [MulMul.comm] at h_it
            rw [← Prod.eq.Mul_ProdTail.of.GtLength_0 (by linarith)] at h_it
            rw [Mul.comm (a := s.prod)] at h_it
            rw [← MulProd_Mul_Prod.eq.Mul_Prod s n d] at h_it
            obtain ⟨i'', j'', h_eq⟩ := Any_EqAddMul.of.Lt_Mul h_it
            obtain ⟨h_i''_eq, h_j''_eq⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_eq.symm
            rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_eq.symm]
            have h_j' := j'.isLt
            obtain ⟨j_i', j_j', h_eq⟩ := Any_EqAddMul.of.Lt_Mul h_j'
            obtain ⟨h_j_i'_eq, h_j_j'_eq⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_eq.symm
            simp [GetRepeat_AddMul.eq.Get.of.Eq_AddMul.fin h_eq.symm]
            have h_j'' := j''.isLt
            obtain ⟨j_i'', j_j'', h_eq⟩ := Any_EqAddMul.of.Lt_Mul h_j''
            obtain ⟨h_j_i''_eq, h_j_j''_eq⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_eq.symm
            simp [GetRepeat_AddMul.eq.Get.of.Eq_AddMul.fin h_eq.symm]
            simp [Get]
            simp [h_i''_eq, h_j_j''_eq, h_j''_eq, h_i'_eq, h_j_j'_eq, h_j'_eq]
            simp [EqAddSub.of.Ge h_d]
            rw [GetSplitAt.of.Lt_Mul_ProdTail.Gt_0.GtGet_0.GtLength_0 h_s h_i h_d h_t X]
            apply Get.of.Flatten.Lt.Lt.Eq.Eq (by simp) (by simp)
            simp_all
            apply SEqFlattenSSplitAt.of.SEq
            ·
              apply SEq_Cast.of.Eq
              simp
            ·
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
      rw [HeadD.eq.Get_0.of.GtLength_0 (by simpa)]
      rw [GetSet.eq.Get_0.of.Gt_0.GtLength_0 h_s h_d]
      rw [ProdTake_1.eq.Get_0.of.GtLength_0 (by simpa)]
      simp
      rw [GetSet.eq.Get_0.of.Gt_0.GtLength_0 h_s h_d]


-- created on 2025-07-05
-- updated on 2026-07-27
