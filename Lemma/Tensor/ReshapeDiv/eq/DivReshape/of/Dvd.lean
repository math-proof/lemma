import Lemma.Tensor.ReshapeBFn.eq.BFnReshape.of.Dvd
open Tensor


@[main]
private lemma main
  [Div α]
  {s' : List ℕ}
-- given
  (h : s.prod ∣ s'.prod)
  (X : Tensor α s)
  (B : Tensor α []) :
-- imply
  (X / B).reshape s' h = X.reshape s' h / B :=
-- proof
  ReshapeBFn.eq.BFnReshape.of.Dvd (· / ·) h X B


-- created on 2026-08-12
-- updated on 2026-08-15
