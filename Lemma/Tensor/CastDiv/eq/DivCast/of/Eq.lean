import Lemma.Tensor.MapCast.as.MapBFn.of.Eq
open Tensor


@[main]
private lemma main
  [Div α]
-- given
  (h : s = s')
  (X : Tensor α s)
  (n : Tensor α []) :
-- imply
  have h := congrArg (Tensor α) h
  cast h (X / n) = cast h X / n :=
-- proof
  Cast_MapBFn.eq.MapCast.of.Eq h X n


-- created on 2025-09-21
-- updated on 2026-08-15
