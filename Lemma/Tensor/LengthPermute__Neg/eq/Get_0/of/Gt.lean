import Lemma.List.GetPermute__Neg.eq.Get_0.of.Gt
import Lemma.Nat.Gt_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import sympy.tensor.Basic
open Nat Tensor List


@[main]
private lemma main
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : i > d)
  (X : Tensor α s) :
-- imply
  (X.permute i (-d)).length = s[0]'(Gt_0 i) := by
-- proof
  rw [Length.eq.Get_0.of.GtLength_0]
  ·
    apply GetPermute__Neg.eq.Get_0.of.Gt h
  ·
    simp
    apply Gt_0 i


-- created on 2025-12-02
