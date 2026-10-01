import Lemma.Nat.Lt.is.All.Lt
open Nat


@[main]
private lemma given
  [Preorder α]
  {x y : Tensor α (n :: s)}
-- given
  (h : ∀ i : Fin n, x[i] < y[i]) :
-- imply
  x < y := by
-- proof
  exact Lt.is.All.Lt.mpr h


-- created on 2022-03-31
