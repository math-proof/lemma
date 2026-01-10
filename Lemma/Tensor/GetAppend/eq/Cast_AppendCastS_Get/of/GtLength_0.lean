import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.GetAppend.as.AppendCastS_Get.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
open Bool Tensor


@[main, fin]
private lemma main
-- given
  (h : b.length > 0)
  (A : Tensor α (b ++ m :: s))
  (B : Tensor α (b ++ n :: s))
  (i : Fin b[0]) :
-- imply
  have : i < A.length := by simp_all [Length.eq.Get_0.of.GtLength_0]
  have : i < B.length := by simp_all [Length.eq.Get_0.of.GtLength_0]
  have h_s : (b ++ m :: s).tail = b.tail ++ m :: s := by grind
  have h_s' : (b ++ n :: s).tail = b.tail ++ n :: s := by grind
  (A ++ B)[i]'(by simp_all [Length.eq.Get_0.of.GtLength_0]) = cast (by grind) (cast (congrArg (Tensor α) h_s) A[i] ++ cast (congrArg (Tensor α) h_s') B[i]) := by
-- proof
  apply Eq_Cast.of.SEq
  apply GetAppend.as.AppendCastS_Get.of.GtLength_0


-- created on 2026-01-10
