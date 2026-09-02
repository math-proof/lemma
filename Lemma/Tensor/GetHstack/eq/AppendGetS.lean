import Lemma.Tensor.GetAppend.eq.AppendGetS
open Tensor


@[main]
private lemma main
-- given
  (A : Tensor α [d, n])
  (B : Tensor α [d, m])
  (i : Fin d) :
-- imply
  (A.hstack B)[i] = id (α := Tensor α [n]) A[i] ++ id (α := Tensor α [m]) B[i] := by
-- proof
  let A' : Tensor α ([d] ++ n :: []) := A
  let B' : Tensor α ([d] ++ m :: []) := B
  apply (congrArg (fun X : Tensor α [d, n + m] => X[i]) (rfl : A.hstack B = A' ++ B')).trans
  apply (GetAppend.eq.AppendGetS A' B' i).trans (by grind)


-- created on 2026-09-01
-- updated on 2026-09-02
