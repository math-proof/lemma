import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.Append
import Lemma.Tensor.GetAppend.as.AppendCastS_Get.of.GtLength_0
open Bool Tensor
set_option maxHeartbeats 500000


@[main]
private lemma main
-- given
  (A : Tensor α ([d] ++ n :: s))
  (B : Tensor α ([d] ++ m :: s))
  (i : Fin d) :
-- imply
  id (α := Tensor α ((n + m) :: s)) (A ++ B)[i] = id (α := Tensor α (n :: s)) A[i] ++ id (α := Tensor α (m :: s)) B[i] := by
-- proof
  simp only [id]
  apply Eq.of.SEq
  have h := GetAppend.as.AppendCastS_Get.of.GtLength_0.fin (b := [d]) (s := s) (by simp) A B i
  simp at h
  apply h.trans
  apply SEq.of.Eq
  have happ := Tensor.Append (A.get i : Tensor α ([] ++ n :: s)) (B.get i : Tensor α ([] ++ m :: s))
  extract_lets A' B' at happ
  refine happ.trans ?_
  simp [A', B', GetElem.getElem]
  rfl


-- created on 2026-08-19
-- updated on 2026-08-19
