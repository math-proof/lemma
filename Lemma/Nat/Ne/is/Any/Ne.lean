import Lemma.Tensor.Eq.is.All_EqGetS
open Tensor


@[main]
private lemma main
  {A B : Tensor α (n :: s)} :
-- imply
  A ≠ B ↔ ∃ i : Fin n, A[i] ≠ B[i] := by
-- proof
  rw [Ne, Eq.is.All_EqGetS]
  exact not_forall


-- created on 2026-09-27
