import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.ProdEraseIdx.eq.MulProdS
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Tensor.DataSum.as.FlattenMapSplitAtData
import Lemma.Tensor.DataUnsqueeze.as.Data
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.EqGetS.of.SEq.Lt
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.SplitAt.eq.UnflattenCast
open Bool Fin List Nat Tensor Vector


@[main]
private lemma main
  [AddZeroClass α]
-- given
  (X : Tensor α s)
  (i : ℕ) :
-- imply
  (X.unsqueeze i).sum i ≃ X := by
-- proof
  apply SEq.of.SEqDataS.Eq (by grind)
  erw [DataSum.eq.Cast_FlattenMapSplitAtData]
  unfold List.Vector.splitAt
  simp
  apply SEqCast.of.SEq.Eq (by simp [MulProdS.eq.ProdEraseIdx])
  apply SEq.of.All_EqGetS.Eq.fin
  ·
    intro t
    have h_t := t.isLt
    have h_t : t < ((s.insertIdx i 1).take i).prod * (((s.insertIdx i 1).drop i).drop 1).prod := by
      grind
    let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
    let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
    rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
    simp
    rw [Vector.GetSum.eq.SumMapGet.fin]
    rw [Tensor.DataUnsqueeze.eq.Cast_Data]
    simp
    rw [UnflattenCast.eq.SplitAt]
    sorry
  ·
    simp [MulProdS.eq.ProdEraseIdx]


-- created on 2026-07-22
