import Lemma.Bool.EqCast.of.SEq
import Lemma.Vector.EqHeadSplitAt_0
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSum.eq.SumMapGet
import Lemma.Vector.Head.eq.Get_0
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import sympy.tensor.tensor
open Bool Vector


@[main, comm]
private lemma main
  [Add α] [Zero α]
-- given
  (X : Tensor α (n :: s)) :
-- imply
  (X.sum 0).data = (X.data.splitAt 1).sum := by
-- proof
  unfold Tensor.sum
  simp
  apply EqCast.of.SEq
  apply SEq.of.All_EqGetS.Eq.fin (by simp)
  intro t
  have h_t := t.isLt
  rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (i := ⟨0, by grind⟩) (j := ⟨t, by grind⟩) (by grind)]
  simp
  rw [Head.eq.Get_0.fin]
  erw [GetSum.eq.SumMapGet.fin]
  erw [GetSum.eq.SumMapGet.fin]
  simp
  congr 1
  congr 1
  congr 1
  apply EqHeadSplitAt_0


-- created on 2026-07-22
