import Lemma.Tensor.ResizeBFn.eq.BFnResize
open Tensor


@[main]
private lemma main
  [MulZeroClass α]
-- given
  (X : Tensor α s)
  (B : Tensor α [])
  (dim : Fin s.length)
  (n : ℕ) :
-- imply
  (X * B).resize dim n = X.resize dim n * B :=
-- proof
  ResizeBFn.eq.BFnResize (zero_mul ·) X B dim n


-- created on 2026-08-15
