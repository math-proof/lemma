import Lemma.Tensor.EqLengthS
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
  apply EqLengthS


-- created on 2025-10-08
