import Lemma.Tensor.Le.is.All.Le
open Tensor


@[main]
private lemma main
  [LE α]
  {x y : Tensor α (n :: s)}
-- given
  (h : ∀ i : Fin n, x[i] ≤ y[i]) :
-- imply
  x ≤ y :=
-- proof
  Le.is.All.Le.mpr h


-- created on 2022-03-31
