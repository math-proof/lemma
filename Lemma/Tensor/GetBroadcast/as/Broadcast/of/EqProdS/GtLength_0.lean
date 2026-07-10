import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.EqProd_0.is.In0
import Lemma.List.TailAppend.eq.AppendTail.of.Ne_Nil
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Tensor.DataGet.as.GetSplitAtData.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool List Nat Tensor Vector


@[main, fin, cast, cast.fin]
private lemma main
  {s s' bz : List ℕ}
-- given
  (h : bz.length > 0)
  (h_s : s.prod = s'.prod)
  (X : Tensor α s)
  (i : Fin bz[0]) :
-- imply
  (X.reshape (bz ++ s') (by simp [h_s]))[i]'(by rw [Length.eq.Get_0.of.GtLength_0 (by grind)]; grind) ≃ X.reshape (bz.tail ++ s') (by simp [h_s]) := by
-- proof
  simp only [GetElem.getElem]
  unfold Tensor.reshape
  apply SEq.of.SEqDataS.Eq
  ·
    grind
  ·
    simp
    rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (i := ⟨i, by grind⟩)]
    ·
      apply SEqCastS.of.SEq.Eq.Eq
      ·
        simp
      ·
        simp [h_s]
        if h_0 : 0 ∈ s then
          right
          rw [List.EqProd_0.of.In0 h_0] at h_s
          apply List.In0.of.EqProd_0 h_s.symm
        else
          left
          rw [EqDivMul.of.Ne_0]
          have := List.NeProd_0.of.NotIn0 h_0
          rwa [h_s] at this
      ·
        simp
        have h_bz : bz ≠ [] := by grind
        apply SEq.of.All_EqGetS.Eq.fin
        ·
          intro j
          rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          simp [TailAppend.eq.AppendTail.of.Ne_Nil h_bz]
          rw [GetCast.eq.Get.of.Eq.fin]
          ·
            simp
            repeat rw [GetRepeat.eq.Get_Mod.fin]
            simp [Mul_Mul.eq.MulMul]
            simp [h_s]
          ·
            simp [h_s]
            if h_0 : 0 ∈ s then
              right
              rw [List.EqProd_0.of.In0 h_0] at h_s
              apply List.In0.of.EqProd_0 h_s.symm
            else
              left
              rw [EqDivMul.of.Ne_0]
              have := List.NeProd_0.of.NotIn0 h_0
              rwa [h_s] at this
        ·
          simp
          if h_0 : 0 ∈ s then
            have h_0 := EqProd_0.of.In0 h_0
            simp [h_0]
            rw [TailAppend.eq.AppendTail.of.Ne_Nil h_bz]
            simp
            right
            rw [h_0] at h_s
            apply List.In0.of.EqProd_0 h_s.symm
          else
            simp [h_s]
            rw [EqDivMul.of.Ne_0]
            ·
              rw [TailAppend.eq.AppendTail.of.Ne_Nil h_bz]
              simp
            ·
              apply NeProd_0.of.NotIn0
              have := List.NeProd_0.of.NotIn0 h_0
              rw [h_s] at this
              apply List.NotIn0.of.NeProd_0 this
    ·
      aesop


-- created on 2026-07-04
