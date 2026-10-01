import Lemma.Nat.Gt.is.All.Gt
open Nat


@[main]
private lemma given
  [Preorder α]
  {x y : Tensor α (n :: s)}
-- given
  (h : ∀ i : Fin n, x[i] > y[i]) :
-- imply
  x > y := by
-- proof
  exact Gt.is.All.Gt.mpr h


-- created on 2022-03-31
