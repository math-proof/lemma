import Lemma.Tensor.Eq.is.All_EqGetS
open Tensor


@[path]
private lemma main
  {A B : Tensor α (n :: s)} :
-- imply
  A = B ↔ ∀ i : Fin n, A[i] = B[i] :=
-- proof
  Eq.is.All_EqGetS A B


-- created on 2023-05-01
