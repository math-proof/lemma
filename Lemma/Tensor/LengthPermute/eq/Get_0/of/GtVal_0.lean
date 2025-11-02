import Lemma.List.GetPermute.eq.Get.of.Lt
import Lemma.Nat.Gt_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import sympy.tensor.Basic
open Nat Tensor List


@[main, comm]
private lemma main
  {i : Fin s.length}
-- given
  (h : i.val > 0)
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  (X.permute i d).length = s[0]'(Gt_0 i) := by
-- proof
  rw [Length.eq.Get_0.of.GtLength_0]
  ·
    apply GetPermute.eq.Get.of.Lt h
  ·
    simp
    apply Gt_0 i


-- created on 2025-11-02
