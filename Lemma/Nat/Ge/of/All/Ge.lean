import Lemma.Nat.Ge.is.All.Ge
open Nat


@[main]
private lemma main
  [LE α]
  {x y : Tensor α (n :: s)}
-- given
  (h : ∀ i : Fin n, x[i] ≥ y[i]) :
-- imply
  x ≥ y :=
-- proof
  Ge.is.All.Ge.mpr h


-- created on 2022-03-31
