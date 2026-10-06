import Lemma.Nat.Gt.is.All.Gt
open Nat


@[main]
private lemma main
  [Preorder α]
  {x y : Tensor α (n :: s)}
-- given
  (h : x > y) :
-- imply
  ∀ i : Fin n, x[i] > y[i] :=
-- proof
  Gt.is.All.Gt.mp h


-- created on 2022-03-31
-- updated on 2022-04-01
