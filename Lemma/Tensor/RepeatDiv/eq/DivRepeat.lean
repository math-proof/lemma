import Instance.Data.Tensor.Defs.Part2
import Lemma.Tensor.RepeatBFn.eq.BFnRepeat
open Tensor


@[path]
private lemma main
  [Div α]
-- given
  (X : Tensor α s)
  (B : Tensor α [])
  (dim : Fin s.length)
  (n : ℕ) :
-- imply
  (X / B).repeat dim n = X.repeat dim n / B :=
-- proof
  RepeatBFn.eq.BFnRepeat (· / ·) X B dim n


-- created on 2026-08-12
-- updated on 2026-11-21
