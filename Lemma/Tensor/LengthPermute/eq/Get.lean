import Lemma.List.GetPermute__Neg.eq.Get.of.GtLength
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import sympy.tensor.tensor
open List Tensor


@[main]
private lemma main
-- given
  (X : Tensor α s)
  (d : Fin s.length) :
-- imply
  (X.permute d (-d)).length = s[d] := by
-- proof
  rw [Length.eq.Get_0.of.GtLength_0]
  ·
    rw [GetPermute__Neg.eq.Get.of.GtLength]
    simp
  ·
    simp
    linarith [d.isLt]


-- created on 2025-11-23
