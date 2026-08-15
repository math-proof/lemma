import Lemma.Tensor.ReshapeBFn.eq.BFnReshape.of.Dvd
open Tensor


@[main]
private lemma main
  [Mul α]
  {s' : List ℕ}
-- given
  (h : s.prod ∣ s'.prod)
  (X : Tensor α s)
  (B : Tensor α []) :
-- imply
  (X * B).reshape s' h = X.reshape s' h * B :=
-- proof
  ReshapeBFn.eq.BFnReshape.of.Dvd (f := (· * · : α → α → α)) h X B


-- created on 2026-08-15
