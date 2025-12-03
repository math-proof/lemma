import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.GetPermute__Neg.eq.Get_0.of.Gt
import Lemma.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
import Lemma.List.TailPermute__Neg.eq.PermuteTail.of.Gt
import Lemma.Nat.ToNatSub_Neg.eq.Add_1
import Lemma.Tensor.DataGet.eq.Cast_GetSplitAtData.of.GtLength_0
import Lemma.Tensor.EqGetS.of.Eq.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthPermute__Neg.eq.Get_0.of.Gt
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.Permute__Neg.as.PermuteTail.of.Val.eq.SubLength_1
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Tensor.SEqPermute__0
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool List Nat Tensor Vector


@[main]
private lemma main
  {s : List ℕ}
  {i k d : ℕ}
-- given
  (h_i : i + 1 < s.length)
  (h_k : k < s[0])
  (h_d : i ≥ d)
  (X : Tensor α s) :
-- imply
  have h_Xk : k < X.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  (X.permute ⟨i + 1, h_i⟩ (-d)).get ⟨k, by rwa [LengthPermute__Neg.eq.Get_0.of.Gt (by simp; omega)]⟩ ≃ (X.get ⟨k, h_Xk⟩).permute ⟨i, by simp; omega⟩ (-d) := by
-- proof
  intro h_Xk
  have h_toNat := ToNatSub_Neg.eq.Add_1 d
  if h_d : d = 0 then
    subst h_d
    simp
    have := SEqPermute__0 (X.get ⟨k, h_Xk⟩) ⟨i, by grind⟩
    apply SEq.symm ∘ SEq.trans this
    apply SEqGetS.of.SEq.GtLength
    apply SEq_Permute__0
  else if h_i0 : i = s.length - 2 then
    have : NeZero d := ⟨h_d⟩
    -- subst h_i0
    rw [@Tensor.Permute.eq.Ite (i := ⟨i, by grind⟩) (d := -d)]
    simp
    split_ifs with h_d0 h_pos h_pos
    ·
      omega
    ·
      omega
    ·
      apply SEq_Cast.of.SEq.Eq
      ·
        simp only [h_toNat]
        rw [Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 (by simp; omega)]
      ·
        rw [h_toNat]
        have := Permute__Neg.as.PermuteTail.of.Val.eq.SubLength_1 (by simp; omega) X (i := ⟨i + 1, h_i⟩) (d := d)
        have := SEqGetS.of.SEq.GtLength.fin (by rwa [LengthPermute__Neg.eq.Get_0.of.Gt (by grind)]) this (i := k)
        apply SEq.trans this
        -- simp only [show s.length - 2 + 1 = s.length - 1 by omega]
        sorry
    ·
      omega
  else
    rw [@Tensor.Permute.eq.Ite (i := ⟨i, by simp; omega⟩) (d := -d)]
    simp
    split_ifs with h_d0? h_i0 h_i_end
    repeat omega
    have := Permute.eq.Ite X ⟨i + 1, by grind⟩ (-d : ℤ)
    have h_i_ne : i + 1 ≠ s.length - 1 := by omega
    simp [h_d, h_d0?, h_i_ne] at this
    have h_k' : k < (s.permute ⟨i + 1, by grind⟩ (-↑d))[0]'(by simp; grind) := by
      rwa [GetPermute__Neg.eq.Get_0.of.Gt (by simp; omega)]
    simp [EqGetS.of.Eq.GtLength_0 (by simp; omega) this ⟨k, h_k'⟩]
    apply SEq.of.SEqDataS.Eq
    ·
      sorry
    ·
      simp
      rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (i := ⟨k, h_k'⟩)]
      apply SEqCastS.of.SEq.Eq.Eq
      ·
        sorry
      ·
        sorry
      ·
        simp
        apply SEq.of.All_EqGetS.Eq.fin
        ·
          intro t
          have h_t := t.isLt
          rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          rw [GetCast.eq.Get.of.Eq.fin]
          ·
            simp [TailPermute__Neg.eq.PermuteTail.of.Gt (show (⟨i + 1, h_i⟩ : Fin s.length) > d by simp; omega)]
            sorry
          ·
            simp only [h_toNat]
            simp [List.Permute__Neg.eq.Append_AppendRotateDropTake]
            simp [Mul_Mul.eq.MulMul]
            repeat rw [EqMin.of.Le (by omega)]
            simp
        ·
          simp only [h_toNat]
          simp
          rw [TailPermute__Neg.eq.PermuteTail.of.Gt (by simp; omega)]
          simp [List.Permute__Neg.eq.Append_AppendRotateDropTake]
          simp [Mul_Mul.eq.MulMul]
          repeat rw [EqMin.of.Le (by omega)]
          simp


-- created on 2025-12-02
-- updated on 2025-12-03
