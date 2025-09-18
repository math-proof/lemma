import sympy.tensor.Basic
import sympy.tensor.tensor
import Lemma.Tensor.EqLength_0.of.Eq_Nil
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
open Tensor


@[main]
private lemma main
  {X : Tensor α s} :
-- imply
  X.length = if h : s.length > 0 then
    s[0]
  else
    0 := by
-- proof
  split_ifs with h
  ·
    apply Length.eq.Get_0.of.GtLength_0 h
  ·
    simp at h
    apply EqLength_0.of.Eq_Nil h


-- created on 2025-06-24
