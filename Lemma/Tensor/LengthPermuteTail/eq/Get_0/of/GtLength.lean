import Lemma.List.GetAppend.eq.Get.of.GtLength
import Lemma.List.GetTake.eq.Get.of.Lt_LengthTake
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import sympy.tensor.Basic
open List Tensor


@[main]
private lemma main
-- given
  (h : s.length > d)
  (X : Tensor α s) :
-- imply
  (X.permuteTail d).length = s[0] := by
-- proof
  rw [Length.eq.Get_0.of.GtLength_0]
  ·
    rw [GetAppend.eq.Get.of.GtLength]
    ·
      rw [GetTake.eq.Get.of.Lt_LengthTake]
    ·
      simpa
  ·
    simp
    omega


-- created on 2025-12-02
