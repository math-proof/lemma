import Lemma.Nat.Lt.is.All.Lt
open Nat


@[path]
private lemma main
  [Preorder α]
  {x y : Tensor α (n :: s)}
-- given
  (h : x < y) :
-- imply
  ∀ i : Fin n, x[i] < y[i] :=
-- proof
  Lt.is.All.Lt.mp h


-- created on 2022-03-31
-- updated on 2022-04-01
