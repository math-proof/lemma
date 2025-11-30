import Lemma.Tensor.EqLength_0.of.Eq_Nil
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import sympy.tensor.functions
open Tensor


@[main]
private lemma main
  [Exp α]
-- given
  (X : Tensor α s) 
  (d : ℕ):
-- imply
  (X.softmax d).length = X.length := by
-- proof
  if h : s.length > 0 then
    repeat rw [Length.eq.Get_0.of.GtLength_0 (by assumption)]
  else
    simp at h
    repeat rw [EqLength_0.of.Eq_Nil (by assumption)]


-- created on 2025-11-30
