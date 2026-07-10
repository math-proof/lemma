import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.EqSwap_0'1
import Lemma.List.InsertIdxAppend.eq.Append_Cons
import Lemma.List.InsertIdxAppend.eq.Append_InsertIdx
import Lemma.List.SwapAppend.eq.Append_Swap.of.LeLength.LeLength
import Lemma.Tensor.Matmul.as.Bmm.of.Eq
import Lemma.Tensor.Matmul.as.BroadcastMatmul.of.EqGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.SEqMulS.of.SEq.SEq
import Lemma.Tensor.SEqRepeatS.of.SEq.EqValS.Eq
import Lemma.Tensor.SEqSumS.of.SEq.Eq
import Lemma.Tensor.SEqTransposeS.of.Eq
import Lemma.Tensor.SEqUnsqueezeS.of.SEq.Eq
open Bool List Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [m, k])
  (B : Tensor α [k, n]) :
-- imply
  let A' : Tensor α [m, 1, k] := A.unsqueeze 1
  let A' : Tensor α [m, n, k] := cast (congrArg (Tensor α) (by simp)) (A'.repeat ⟨1, by grind⟩ n)
  let B' : Tensor α [n, k] := Bᵀ
  let B' : Tensor α [1, n, k] := B'.unsqueeze 0
  let B' : Tensor α [m, n, k] := cast (congrArg (Tensor α) (by simp)) (B'.repeat ⟨0, by grind⟩ m)
  A @ B = (A' * B').sum 2 := by
-- proof
  simp [Dot.dot]
  simp [Tensor.bmm]
  congr 1


-- created on 2026-07-10
