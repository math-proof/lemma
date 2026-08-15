import Lemma.Tensor.UnsqueezeBFn.eq.BFnUnsqueeze
open Tensor


@[main]
private lemma main
  [Mul α]
-- given
  (X : Tensor α s)
  (B : Tensor α [])
  (dim : ℕ) :
-- imply
  (X * B).unsqueeze dim = X.unsqueeze dim * B :=
-- proof
  UnsqueezeBFn.eq.BFnUnsqueeze (f := (· * · : α → α → α)) X B dim


-- created on 2026-08-15
-- updated on 2026-08-16
