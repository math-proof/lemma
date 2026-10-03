import Lemma.Nat.Ne.is.Any.Ne
open Tensor


@[main]
private lemma main
  {A B : Tensor α (n :: s)}
-- given
  (h : ∃ i : Fin n, A[i] ≠ B[i]) :
-- imply
  A ≠ B :=
-- proof
  Nat.Ne.is.Any.Ne.mpr h


-- created on 2023-05-01
