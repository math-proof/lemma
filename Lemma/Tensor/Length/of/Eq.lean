import Lemma.Tensor.Length
open Tensor


@[main]
private lemma main
-- given
  (h : s = s')
  (A : Tensor α s)
  (B : Tensor α s') :
-- imply
  A.length = B.length := by
-- proof
  subst h
  apply Length


-- created on 2025-10-08
