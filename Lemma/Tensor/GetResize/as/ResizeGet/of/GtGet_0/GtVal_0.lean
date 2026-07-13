import Lemma.Nat.Ne_0.of.GtMul
import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength
import Lemma.List.ProdTail.eq.MulProdTakeTail
import Lemma.Nat.DivAdd.eq.AddDivS.of.Dvd
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.ModAddMul.eq.Mod
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.DropTail.eq.Drop
import Lemma.List.GetSet.eq.Get_0.of.Gt_0.GtLength_0
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.List.ProdSet.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.List.ProdTake.eq.Mul_ProdTakeTail.of.Gt_0.GtLength_0
import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.List.ProdTake_1.eq.HeadD_1
import Lemma.List.TailSet.eq.SetTail.of.Gt_0
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.Ge_1.of.Gt_0
import Lemma.Nat.Gt_0
import Lemma.Nat.Mul
import Lemma.Nat.MulMul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.Mul_Mul
import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Tensor.LengthResize.eq.Length.of.GtVal_0
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetCast_Map.eq.UFnGet.of.Eq.Lt
import Lemma.Vector.GetFlatten.eq.Get.of.Lt_Mul
import Lemma.Vector.GetResize.eq.Ite_Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool List Nat Tensor Vector
set_option maxHeartbeats 1000000


@[main, fin, cast, cast.fin]
private lemma main
  [Zero α]
  {d : Fin s.length}
-- given
  (h_d : d.val > 0)
  (h_i : i < s[0])
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  have := GtLength.of.GtLength_0 (by grind) X ⟨i, by grind⟩
  (X.resize d n)[i]'(by rwa [LengthResize.eq.Length.of.GtVal_0 h_d]) ≃ X[i].resize ⟨d - 1, by grind⟩ n := by
-- proof
  simp
  simp only [GetElem.getElem]
  unfold Tensor.resize
  simp [Tensor.get]
  simp [Tensor.toVector]
  obtain ⟨X⟩ := X
  have h_s := Gt_0 d
  have h_d := Ge_1.of.Gt_0 h_d
  simp only [GetElem.getElem]
  rw [GetCast.eq.Get.of.Eq.fin]
  ·
    simp
    apply SEq.of.SEqDataS.Eq
    ·
      rw [← TailSet.eq.SetTail.of.Gt_0 (by assumption)]
    ·
      simp
      apply SEqCastS.of.SEq.Eq.Eq
      ·
        simp
      ·
        rw [ProdSet.eq.MulProd_Mul_Prod.of.GtLength]
        grind
      ·
        rw [GetCast_Map.eq.UFnGet.of.Eq.Lt.fin]
        ·
          simp
          have h_prodset := ProdSet.eq.MulProd_Mul_Prod.of.GtLength (by grind) n (i := d - 1) (s := s.tail)
          rw [EqAddSub.of.Ge (by grind)] at h_prodset
          rw [SetTail.eq.TailSet.of.Gt_0 (by grind)] at h_prodset
          apply SEq.of.All_EqGetS.Eq
          ·
            intro t
            have h_t := t.isLt
            simp at h_t
            simp only [GetElem.getElem]
            rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
            rw [GetCast.eq.Get.of.Eq.fin]
            ·
              repeat rw [GetFlatten.eq.Get.of.Lt_Mul]
              ·
                simp
                repeat rw [GetResize.eq.Ite_Get_Mod.fin]
                simp
                split_ifs with h? h_lt h_lt'
                ·
                  repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                  rw [GetCast.eq.Get.of.Eq.fin (by simp)]
                  rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                  congr 1
                  simp
                  rw [EqAddSub.of.Ge (by grind)]
                  simp at h_prodset
                  simp [h_prodset] at *
                  rw [ProdTail.eq.MulProdTakeTail (d := d - 1)]
                  rw [EqAddSub.of.Ge (by grind)]
                  rw [ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength d.isLt]
                  conv_lhs =>
                    pattern (_ * (_ * _) + _) % _
                    rw [Mul_Mul.eq.MulMul]
                    rw [Nat.ModAddMul.eq.Mod]
                  conv_lhs =>
                    pattern (_ * (_ * _) + _) / _
                    rw [Mul_Mul.eq.MulMul]
                    rw [DivAdd.eq.AddDivS.of.Dvd (by simp)]
                    simp
                    rw [Nat.EqDivMul.of.Ne_0 (Nat.Ne_0.of.GtMul h_t)]
                  grind
                ·
                  rw [h_prodset, Mul_Mul.eq.MulMul] at h?
                  simp at h?
                  grind
                ·
                  rw [h_prodset, Mul_Mul.eq.MulMul] at h?
                  simp at h?
                  grind
                ·
                  rfl
              ·
                rw [EqAddSub.of.Ge (by grind)]
                rw [TailSet.eq.SetTail.of.Gt_0 (by grind)] at h_t
                rw [ProdSet.eq.MulProd_Mul_Prod.of.GtLength (by grind)] at h_t
                convert h_t
                omega
              ·
                simp
                rw [Drop.eq.DropTail s d]
                rw [ProdTake.eq.Mul_ProdTakeTail.of.Gt_0.GtLength_0 h_s h_d]
                rw [MulMul.eq.Mul_Mul]
                rw [TailSet.eq.SetTail.of.Gt_0 (by grind)]
                rw [← h_prodset]
                rw [SetTail.eq.TailSet.of.Gt_0 (by grind)]
                apply AddMul.lt.Mul.of.Lt.Lt h_i h_t
            ·
              rw [ProdSet.eq.MulProd_Mul_Prod.of.GtLength d.isLt]
          ·
            simp
            rw [EqAddSub.of.Ge (by grind)]
            rwa [Drop.eq.DropTail s d]
        ·
          rwa [ProdTake_1.eq.Get_0.of.GtLength_0]
        ·
          rw [ProdTake_1.eq.HeadD_1]
  ·
    rw [HeadD.eq.Get_0.of.GtLength_0 (by simpa)]
    rw [GetSet.eq.Get_0.of.Gt_0.GtLength_0 h_s h_d]
    rw [ProdTake_1.eq.Get_0.of.GtLength_0 (by simpa)]
    rw [GetSet.eq.Get_0.of.Gt_0.GtLength_0 h_s h_d]


-- created on 2026-07-12
-- updated on 2026-07-13
