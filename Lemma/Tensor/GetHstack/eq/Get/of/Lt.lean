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
  have : j < n + m := by grind
  id (α := Tensor α []) (A.hstack B)[i][j] = id (α := Tensor α []) A[i][j] := by
-- proof
  intro
  apply (congrArg (fun t : Tensor α [n + m] => t[j]) (by simpa [id] using GetHstack.eq.AppendGetS A B i)).trans
  apply GetAppend.eq.Get.of.Lt h


-- created on 2026-09-01
-- updated on 2026-09-02
