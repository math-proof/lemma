import Lemma.Tensor.Eq.is.EqDataS
open Tensor


@[main]
private lemma main
  [Inhabited α]
  {a b : Tensor α s}
-- given
  (h : a.data = b.data) :
-- imply
  a = b :=
-- proof
  Eq.is.EqDataS.mpr h


-- created on 2025-05-06
