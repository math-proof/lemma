import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.EqProd_0.is.In0
import Lemma.List.TailAppend.eq.AppendTail.of.Ne_Nil
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Tensor.DataGet.eq.Cast_GetSplitAtData.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Vector List Bool Nat Tensor


@[main, fin]
private lemma main
  {s s' : List ℕ}
-- given
  (h : s'.length > 0)
  (X : Tensor α s)
  (i : Fin s'[0]) :
-- imply
  (X.broadcast (s' ++ s) (by simp))[i]'(by rw [Length.eq.Get_0.of.GtLength_0 (by grind)]; grind) ≃ X.broadcast (s'.tail ++ s) (by simp) := by
-- proof
  simp only [GetElem.getElem]
  unfold Tensor.broadcast
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
        simp
        if h_s : 0 ∈ s then
          right
          assumption
        else
          left
          rw [EqDivMul.of.Ne_0]
          apply NeProd_0.of.NotIn0 h_s
      ·
        simp
        have h_s' : s' ≠ [] := by grind
        apply SEq.of.All_EqGetS.Eq.fin
        ·
          intro j
          rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          simp [TailAppend.eq.AppendTail.of.Ne_Nil h_s']
          rw [GetCast.eq.Get.of.Eq.fin]
          ·
            simp
            repeat rw [GetRepeat.eq.Get_Mod.fin]
            simp [Mul_Mul.eq.MulMul]
          ·
            simp
            if h_s : 0 ∈ s then
              right
              assumption
            else
              left
              rw [EqDivMul.of.Ne_0]
              apply NeProd_0.of.NotIn0 h_s
        ·
          simp
          if h_s : 0 ∈ s then
            have h_s := EqProd_0.of.In0 h_s
            simp [h_s]
            rw [TailAppend.eq.AppendTail.of.Ne_Nil h_s']
            simp
            right
            assumption
          else
            rw [EqDivMul.of.Ne_0]
            ·
              rw [TailAppend.eq.AppendTail.of.Ne_Nil h_s']
              simp
            ·
              apply NeProd_0.of.NotIn0 h_s
    ·
      aesop


-- created on 2026-01-12
