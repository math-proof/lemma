import Lemma.Tensor.Le.is.All.Le
open Tensor


@[path]
private lemma main
  [LE α]
  {x y : Tensor α (n :: s)}
-- given
  (h : x ≤ y) :
-- imply
  ∀ i : Fin n, x[i] ≤ y[i] :=
-- proof
  Le.is.All.Le.mp h


-- created on 2022-03-31
-- updated on 2022-04-01
