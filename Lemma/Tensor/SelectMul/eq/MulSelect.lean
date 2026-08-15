import Lemma.Tensor.SelectBFn.eq.BFnSelect
open Tensor


@[main]
private lemma main
  [Mul α]
-- given
  (X : Tensor α s)
  (B : Tensor α [])
  (d : Fin s.length)
  (i : Fin s[d]) :
-- imply
  (X * B).select d i = X.select d i * B :=
-- proof
  SelectBFn.eq.BFnSelect (f := (· * · : α → α → α)) X B d i


-- created on 2026-08-15
