import Lemma.Tensor.Eq.is.All_EqGetS
open Tensor


@[main]
private lemma main
  {A B : Tensor α (n :: s)}
-- given
  (h : A ≠ B) :
-- imply
  ∃ i : Fin n, A[i] ≠ B[i] :=
-- proof
  not_forall.mp (fun h' => h ((Eq.is.All_EqGetS A B).mpr h'))


-- created on 2023-05-01
