import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.GetPermute.eq.Get.of.Lt
import Lemma.List.Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.TailPermute.eq.PermuteTail.of.GtLength_Add_1
import Lemma.Nat.LtVal
import Lemma.Tensor.DataGet.eq.Cast_GetSplitAtData.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthPermute.eq.Get_0.of.GtVal_0
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import stdlib.SEq
import sympy.tensor.tensor
open Bool List Tensor Vector Nat


@[main]
private lemma main
  [NeZero (d : ℕ)]
  {s : List ℕ}
  {k : ℕ}
-- given
  (h : s.length > 1)
  (h_k : k < s[0])
  (X : Tensor α s) :
-- imply
  (X.permute ⟨1, by omega⟩ d).get ⟨k, by rwa [LengthPermute.eq.Get_0.of.GtVal_0 (by simp)]⟩ ≃ (X.get ⟨k, by rwa [Length.eq.Get_0.of.GtLength_0]⟩).permute ⟨0, by simp; omega⟩ d := by
-- proof
  rw [@Tensor.Permute.eq.Ite (i := ⟨0, by simp; omega⟩) (d := d)]
  simp
  have h_d := NeZero.pos d
  split_ifs with h_d0
  ·
    omega
  ·
    apply SEq_Cast.of.SEq.Eq
    ·
      rw [Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0]
    ·
      unfold permuteHead
      simp
      apply SEq.of.SEqDataS.Eq
      ·
        rw [TailPermute.eq.PermuteTail.of.GtLength_Add_1 h]
        rw [Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0]
      ·
        simp
        rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (by simp; omega) (X.permute ⟨1, h⟩ d) ⟨k, by rwa [GetPermute.eq.Get.of.Lt (by simp)]⟩]
        apply SEqCastS.of.SEq.Eq.Eq
        ·
          simp
        ·
          rw [MulProdS.eq.ProdAppend]
        ·
          simp
          have h_prod : ((s.permute ⟨1, h⟩ ↑d).drop 1).prod = ((s.tail.take (d + 1)).rotate 1).prod * (s.tail.drop (d + 1)).prod := by
            simp [TailPermute.eq.PermuteTail.of.GtLength_Add_1 h]
            simp [Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0]
          apply SEq.of.All_EqGetS.Eq.fin h_prod
          intro t
          have h_t := LtVal t
          simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          sorry


-- created on 2025-11-02
