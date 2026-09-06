import Lemma.Bool.EqCast.of.SEq
import Lemma.Vector.EqHeadSplitAt_0
import Lemma.Vector.GetMap.eq.UFnGet
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetProd.eq.ProdMapGet
import Lemma.Vector.Head.eq.Get_0
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import sympy.tensor.tensor
open Bool Vector


@[main, comm]
private lemma main
  [Mul α] [One α]
-- given
  (X : Tensor α (n :: s)) :
-- imply
  (X.prod 0).data = (X.data.splitAt 1).prod := by
-- proof
  unfold Tensor.prod
  simp
  apply EqCast.of.SEq
  apply SEq.of.All_EqGetS.Eq.fin (by simp)
  intro t
  have h_t := t.isLt
  rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (i := ⟨0, by grind⟩) (j := ⟨t, by grind⟩) (by grind)]
  simp
  rw [Head.eq.Get_0.fin]
  erw [GetMap.eq.UFnGet.fin]
  erw [GetProd.eq.ProdMapGet.fin]
  erw [GetProd.eq.ProdMapGet.fin]
  simp
  congr 1
  congr 1
  congr 1
  apply EqHeadSplitAt_0


-- created on 2026-09-06
