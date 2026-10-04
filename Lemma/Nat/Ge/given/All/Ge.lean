import Lemma.Nat.Ge.is.All.Ge

open Tensor


@[main]
private lemma main
  [LE α]
  {x y : Tensor α (n :: s)}
-- given
  (h : x ≥ y) :
-- imply
  ∀ i : Fin n, x[i] ≥ y[i] := by
-- proof
  exact Nat.Ge.is.All.Ge.mp h


-- created on 2022-03-31
-- updated on 2022-04-01
