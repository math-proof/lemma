import Lemma.Tensor.Eq.is.All_EqGetS
open Tensor


@[main]
private lemma main
  {A B : Tensor α (n :: s)}
-- given
  (h : A = B) :
-- imply
  ∀ i : Fin n, A[i] = B[i] :=
-- proof
  (Eq.is.All_EqGetS A B).mp h


-- created on 2023-03-18
