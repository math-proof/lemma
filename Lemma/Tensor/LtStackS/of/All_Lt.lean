import Lemma.Tensor.BFnStackS.of.All_BFn.All_Iff_All_BFnGetSData
import Lemma.Tensor.Lt.is.LtDataS
open Tensor


@[main]
private lemma main
  [Preorder α]
  {X Y : Fin n → Tensor α s}
-- given
  (h : ∀ i : Fin n, X i < Y i) :
-- imply
  [i < n] X i < [i < n] Y i :=
-- proof
  BFnStackS.of.All_BFn.All_Iff_All_BFnGetSData (R := LT.lt) (R₀ := LT.lt) Lt.is.LtDataS h


-- created on 2026-07-27
-- updated on 2026-07-28
