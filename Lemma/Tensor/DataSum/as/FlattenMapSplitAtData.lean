import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.Drop.eq.Nil.of.LeLength
import Lemma.List.DropDrop.eq.Drop_Add
import Lemma.List.EqEraseIdx.of.LeLength
import Lemma.List.EqTake.of.LeLength
import Lemma.List.ProdDrop.eq.One.of.LeLength
import Lemma.Tensor.DataCast.as.Data.of.Eq
import Lemma.Tensor.DataSum.as.SumSplitAtData.of.GtLength
import Lemma.Tensor.Sum.as.Sum.of.LeLength
import Lemma.Vector.FlattenCast.as.Flatten.of.Eq.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetSum.eq.SumMapGet
import Lemma.Vector.MapCast.as.Map.of.Eq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.SplitAt.as.VectorList.of.LeLength
import Lemma.Vector.Sum.eq.Head.of.Eq_1
open Bool List Tensor Vector


@[main, comm, cast]
private lemma main
  [AddZeroClass α]
-- given
  (X : Tensor α s)
  (i : ℕ) :
-- imply
  (X.sum i).data ≃ ((X.data.splitAt i).map fun x => (x.splitAt 1).sum).flatten := by
-- proof
  if h : i < s.length then
    apply DataSum.as.SumSplitAtData.of.GtLength h
  else
    have h : i ≥ s.length := by grind
    rw [Sum.eq.Cast_Sum.of.LeLength (by grind)]
    rw [DataCast.eq.Cast_Data.of.Eq (Eq_EraseIdx.of.LeLength h)]
    apply SEqCast.of.SEq.Eq (by rw [EqEraseIdx.of.LeLength h])
    rw [SplitAt.eq.Cast_VectorList.of.LeLength h]
    rw [MapCast.eq.Cast_Map.of.Eq (by simp [EqTake.of.LeLength h])]
    rw [FlattenCast.eq.Cast_Flatten.of.Eq.Eq (by simp [EqTake.of.LeLength h]) (by grind)]
    apply SEq_Cast.of.SEq.Eq (by simp [EqTake.of.LeLength h])
    simp
    apply SEq.of.All_EqGetS.Eq.fin
    ·
      intro t
      have h_t := t.isLt
      rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (i := ⟨t, by grind⟩) (j := ⟨0, by rw [DropDrop.eq.Drop_Add]; erw [ProdDrop.eq.One.of.LeLength (by grind)]; grind⟩) (by simp; erw [ProdDrop.eq.One.of.LeLength (by grind)]; grind)]
      simp
      rw [GetSum.eq.SumMapGet.fin]
      rw [Sum.eq.Head.of.Eq_1 (by erw [Drop.eq.Nil.of.LeLength (by grind)]; grind)]
      simp [GetElem.getElem]
      rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
      simp [List.Vector.get]
      rfl
    ·
      simp
      erw [ProdDrop.eq.One.of.LeLength (by grind)]
      simp


-- created on 2026-07-22
