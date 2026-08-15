import Lemma.Tensor.ResizeBFn.eq.BFnResize
open Tensor


@[main]
private lemma main
  [GroupWithZero α]
-- given
  (X : Tensor α s)
  (B : Tensor α [])
  (dim : Fin s.length)
  (n : ℕ) :
-- imply
  (X / B).resize dim n = X.resize dim n / B :=
-- proof
  ResizeBFn.eq.BFnResize (zero_div ·) X B dim n


-- created on 2026-08-12
-- updated on 2026-08-15
