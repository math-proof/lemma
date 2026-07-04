import Lemma.List.GetPermute.eq.Get.of.Gt
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import sympy.tensor.Basic
open Tensor List


@[main]
private lemma main
  {i : Fin s.length}
-- given
  (h : i.val > 0)
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  (X.permute i d).length = s[0]'(by grind) := by
-- proof
  rw [Length.eq.Get_0.of.GtLength_0]
  ·
    apply GetPermute.eq.Get.of.Gt h
  ·
    simp
    grind


-- created on 2025-11-02
