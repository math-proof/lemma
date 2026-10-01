import Lemma.Tensor.Eq_Stack
open Tensor


@[main]
private lemma main
-- given
  (X : Tensor α (n :: s)) :
-- imply
  X = [i < n] X[i] :=
-- proof
  Eq_Stack X


-- created on 2026-09-27
