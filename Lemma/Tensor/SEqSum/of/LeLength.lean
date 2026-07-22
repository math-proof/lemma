import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.DropDrop.eq.Drop_Add
import Lemma.List.EqEraseIdx.of.LeLength
import Lemma.List.EqTake.of.LeLength
import Lemma.List.ProdDrop.eq.One.of.LeLength
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.FlattenCast.as.Flatten.of.Eq.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSum.eq.SumMapGet
import Lemma.Vector.MapCast.as.Map.of.Eq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.SplitAt.as.VectorList.of.LeLength
import Lemma.Vector.Sum.eq.Head.of.Eq_1
import sympy.tensor.tensor
open Bool List Tensor Vector


@[main, comm, cast]
private lemma main
  [AddZeroClass α]
  {d : ℕ}
-- given
  (h : s.length ≤ d)
  (X : Tensor α s) :
-- imply
  X.sum d ≃ X := by
-- proof
  unfold Tensor.sum
  apply SEq.of.SEqDataS.Eq
  ·
    rwa [EqEraseIdx.of.LeLength]
  ·
    have hd : d ≥ s.length := h
    have h_drop_prod : ((s.drop d).drop 1).prod = 1 := by
      rw [List.Drop.eq.Nil.of.LeLength (by grind)]
      simp
    apply SEqCast.of.SEq.Eq (by simp; grind)
    rw [SplitAt.eq.Cast_VectorList.of.LeLength hd]
    rw [MapCast.eq.Cast_Map.of.Eq (by simp [EqTake.of.LeLength hd])]
    rw [FlattenCast.eq.Cast_Flatten.of.Eq.Eq (by simp [EqTake.of.LeLength hd]) (by grind)]
    refine SEqCast.of.SEq.Eq (by simp [EqTake.of.LeLength hd]) ?_
    simp
    apply SEq.of.All_EqGetS.Eq.fin
    ·
      intro t
      have h_t := t.isLt
      rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (i := ⟨t, by grind⟩) (j := ⟨0, by grind⟩) (by grind)]
      simp
      rw [GetSum.eq.SumMapGet.fin]
      rw [Sum.eq.Head.of.Eq_1 (by rw [List.Drop.eq.Nil.of.LeLength (by grind)]; grind)]
      simp [GetElem.getElem]
      rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
      simp [List.Vector.get]
    ·
      rw [h_drop_prod]
      simp


-- created on 2025-06-23
-- updated on 2026-07-22
