import Lemma.Tensor.SelectBFn.eq.BFnSelect
open Tensor


@[main]
private lemma main
  [Div α]
-- given
  (X : Tensor α s)
  (B : Tensor α [])
  (d : Fin s.length)
  (i : Fin s[d]) :
-- imply
  (X / B).select d i = X.select d i / B :=
-- proof
  SelectBFn.eq.BFnSelect (· / ·) X B d i


-- created on 2026-08-12
-- updated on 2026-08-15
