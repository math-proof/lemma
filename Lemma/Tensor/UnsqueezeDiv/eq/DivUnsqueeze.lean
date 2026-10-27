import Lemma.Tensor.UnsqueezeBFn.eq.BFnUnsqueeze
import Def.Data.Holor.Unsqueeze
open Tensor


@[path]
private lemma main
  [Div α]
-- given
  (X : Tensor α s)
  (B : Tensor α [])
  (dim : ℕ) :
-- imply
  (X / B).unsqueeze dim = X.unsqueeze dim / B :=
-- proof
  UnsqueezeBFn.eq.BFnUnsqueeze (· / ·) X B dim


-- created on 2026-08-12
-- updated on 2026-10-26
