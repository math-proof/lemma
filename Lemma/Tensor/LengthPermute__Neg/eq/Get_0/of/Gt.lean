import Lemma.List.GetPermute__Neg.eq.Get_0.of.Gt
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import sympy.tensor.Basic
open Tensor List


@[main]
private lemma main
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : i > d)
  (X : Tensor α s) :
-- imply
  (X.permute i (-d)).length = s[0]'(by grind) := by
-- proof
  rw [Length.eq.Get_0.of.GtLength_0]
  ·
    apply GetPermute__Neg.eq.Get_0.of.Gt h
  ·
    simp
    grind


-- created on 2025-12-02
