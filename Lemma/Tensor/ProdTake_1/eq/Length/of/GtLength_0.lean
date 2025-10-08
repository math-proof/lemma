import sympy.tensor.Basic
import Lemma.Tensor.GtLength_0.of.GtLength_0
import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
open Tensor List


@[main, comm]
private lemma main
  {X : Tensor α s}
-- given
  (h : X.length > 0) :
-- imply
  (s.take 1).prod = X.length := by
-- proof
  have h_s := GtLength_0.of.GtLength_0 h
  rw [ProdTake_1.eq.Get_0.of.GtLength_0 h_s]
  rw [Length.eq.Get_0.of.GtLength_0]


-- created on 2025-10-08
