import Lemma.Nat.Ge.is.All.Ge
open Nat


@[main]
private lemma main
  [LE α]
  {x y : Tensor α (n :: s)}
-- given
  (h : x ≥ y) :
-- imply
  ∀ i : Fin n, x[i] ≥ y[i] :=
-- proof
  Ge.is.All.Ge.mp h


-- created on 2026-09-27
