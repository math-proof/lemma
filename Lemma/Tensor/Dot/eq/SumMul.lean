import Lemma.Tensor.SEqResize.of.Eq_Get
import Lemma.Tensor.Matmul.as.Bmm
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Tensor.Select_0.as.Get.of.GtGet_0.GtLength_0
import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.SEqMulS.of.SEq.SEq
import Lemma.Tensor.SEqSelectS.of.SEq
import Lemma.Tensor.SEqSumS.of.SEq
open Bool Tensor


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
