import Lemma.Tensor.Lt.is.LtDataS
import Lemma.Tensor.BFnStackS.of.All_BFn.All_Iff_All_BFnGetSData
import sympy.tensor.stack
open Tensor


@[main]
private lemma main
  [Preorder α]
  {X Y : Fin n → Tensor α s}
-- given
  (h : ∀ i : Fin n, X i < Y i) :
-- imply
  [i < n] X i < [i < n] Y i :=
  BFnStackS.of.All_BFn.All_Iff_All_BFnGetSData (R := LT.lt) (R₀ := LT.lt) (hDataS := Lt.is.LtDataS) h


-- created on 2026-07-27
