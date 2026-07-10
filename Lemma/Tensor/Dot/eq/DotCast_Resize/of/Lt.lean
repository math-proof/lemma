import Lemma.Tensor.Resize.as.FromVectorMapToVector.of.GtVal_0
import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Fin.Eq_0
import Lemma.Fin.Eq_Fin.of.EqVal
import Lemma.List.EqSwap_0'1
import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.List.ProdSwap.eq.Prod
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Div.eq.One.of.Ne_0
import Lemma.Nat.EqAddMulDiv
import Lemma.Nat.EqDivAddMul.of.Lt
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.EqMulDiv
import Lemma.Nat.EqMulS.of.Eq
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Tensor.DataAppend.as.AppendDataS
import Lemma.Tensor.DataAppend.as.FlattenMap₂_CastS_SplitAtData
import Lemma.Tensor.DataCast.as.Data.of.Eq
import Lemma.Tensor.DataGet.eq.GetUnflattenData
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.DataTransposeTensor.eq.Cast
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqAppendS
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.EqGet0_0
import Lemma.Tensor.EqRepeatS.of.Eq
import Lemma.Tensor.EqUnsqueezeS.of.Eq
import Lemma.Tensor.GetAppend.as.AppendCastS_Get.of.GtLength_0
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetRepeat.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.Lt_Get_0.GtVal_0
import Lemma.Tensor.GetSelect_1.as.Get.of.Lt_Get_0.Lt_Get_1.GtLength_1
import Lemma.Tensor.GetSum_2.eq.SumGet__0
import Lemma.Tensor.GetSum_2.eq.SumGet__1
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0
import Lemma.Tensor.Get_0.eq.TensorCast_Data
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.HeadDataSum.eq.SumData
import Lemma.Tensor.Matmul.as.BroadcastMatmul.of.LtGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.Matmul.as.BroadcastMatmul.of.EqGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.Matmul.as.SelectBatchDot.of.LtGet_SubLength_1.GeLength_2
import Lemma.Tensor.Matmul.as.SelectBatchDot.of.Lt_Get_SubLength.GeLength_2
import Lemma.Tensor.Matmul.eq.SumMulDataS.of.Lt
import Lemma.Tensor.SEqDataS.of.SEq
import Lemma.Tensor.SEqSumS.of.SEq
import Lemma.Tensor.Select_0.as.Get.of.GtLength_0
import Lemma.Vector.Cast_Cast.eq.Cast.of.Eq.Eq
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.EqGet0_0
import Lemma.Vector.EqSumS.of.SEq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetFlatten_AddMul.eq.Get.of.Lt.Lt.Eq
import Lemma.Vector.GetMap₂.eq.BFnGetS
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.Repeat.eq.Cast.of.Eq_1
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.SplitAt0.eq.Zero
open Bool Fin List Nat Tensor Vector
set_option maxHeartbeats 10000000


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h : k < n')
  (X : Tensor α [n, k])
  (Y : Tensor α [n', k']) :
-- imply
  X @ Y = (X.resize ⟨1, by grind⟩ n') @ Y := by
-- proof
  unfold Tensor.resize
  simp [Dot.dot]
  conv_rhs => rw [Matmul.eq.Cast_BroadcastMatmul.of.EqGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by simp)]
  rw [Matmul.eq.Cast_BroadcastMatmul.of.LtGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by simpa)]
  apply EqCastS.of.SEq.Eq
  .
    simp [broadcast_shape, matmul_shape]
  .
    simp
    rw [Resize.eq.Cast_FromVectorMapToVector.of.GtVal_0 _ (by simp)]
    simp
    rfl


-- created on 2026-07-10
