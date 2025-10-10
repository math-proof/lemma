import sympy.tensor.Basic
import Lemma.Tensor.Length.eq.Get_0.of.Ne_Nil
import Lemma.List.Ne_Nil.is.GtLength_0
open Tensor List


@[main, comm]
private lemma main
-- given
  (h : s.length > 0)
  (X : Tensor α s) :
-- imply
  X.length = s[0] := by
-- proof
  simp [Length.eq.Get_0.of.Ne_Nil (Ne_Nil.of.GtLength_0 h)]


-- created on 2025-06-14
-- updated on 2025-10-10
