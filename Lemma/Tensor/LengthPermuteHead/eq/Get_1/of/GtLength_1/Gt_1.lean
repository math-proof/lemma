import Lemma.List.GetAppend.eq.Get.of.Lt_Length
import Lemma.List.GetRotate.eq.Ite.of.GeLength.Lt_Length
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import sympy.tensor.Basic
open List Tensor


@[main, comm]
private lemma main
-- given
  (h_d : d > 1)
  (h : s.length > 1)
  (X : Tensor α s) :
-- imply
  (X.permuteHead d).length = s[1] := by
-- proof
  rw [Length.eq.Get_0.of.GtLength_0]
  ·
    rw [GetAppend.eq.Get.of.Lt_Length]
    ·
      rw [GetRotate.eq.Ite.of.GeLength.Lt_Length]
      ·
        split_ifs with h_pos
        ·
          simp
        ·
          simp at h_pos
          grind
      ·
        simp
        omega
      ·
        simp
        omega
    ·
      simp
      omega
  ·
    simp
    left
    omega


-- created on 2025-11-03
