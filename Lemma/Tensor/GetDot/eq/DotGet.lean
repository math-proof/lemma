import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetSum_2.eq.SumGet__1
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Lt_Get_0.Eq.GtLength_0
open List Tensor


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α [n, k])
  (Y : Tensor α [n', k'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil h_s (by apply GeLength_1.of.Ne_Nil h_s) X Y i) = X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  simp [MatMul.dot]
  unfold Tensor.matmul
  simp
  split_ifs with h
  ·
    simp [h]
    simp [broadcast_matmul, broadcast_matmul_rec, batch_dot, broadcast_shape]
    simp [GetSum_2.eq.SumGet__1.fin]
    simp [GetMul.eq.MulGetS.fin]
    -- rw [Tensor.GetCast.eq.Cast_Get.of.Lt_Get_0.Eq.GtLength_0.fin]
    -- rw [Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin]
    simp_all
    sorry
  ·
    sorry


-- created on 2026-01-05
