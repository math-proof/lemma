import Lemma.Tensor.GetAppend.eq.Get.of.Lt
import Lemma.Tensor.GetHstack.eq.AppendGetS
open Tensor


@[main]
private lemma main
-- given
  (h : j < n)
  (A : Tensor α [d, n])
  (B : Tensor α [d, m])
  (i : Fin d) :
-- imply
  (A.hstack B)[i][j]'(by grind) = A[i][j] := by
-- proof
  apply (congrArg (fun t : Tensor α [n + m] => t[j]'(by grind)) (by simpa using GetHstack.eq.AppendGetS A B i)).trans
  apply GetAppend.eq.Get.of.Lt h


-- created on 2026-09-01
-- updated on 2026-09-02
