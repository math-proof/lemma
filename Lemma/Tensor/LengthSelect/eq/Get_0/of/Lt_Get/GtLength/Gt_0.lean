import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import sympy.tensor.tensor
open Tensor


@[main]
private lemma main
-- given
  (h_pos : d > 0)
  (h_d : s.length > d)
  (h_i : i < s[d])
  (X : Tensor α s) :
-- imply
  (X.select ⟨d, h_d⟩ ⟨i, h_i⟩).length = s[0] := by
-- proof
  rw [Length.eq.Get_0.of.GtLength_0]
  ·
    simp
    rwa [List.GetEraseIdx.eq.Get.of.Gt.GtLength h_d]
  ·
    simp
    rw [List.LengthEraseIdx.eq.SubLength_1.of.GtLength h_d]
    omega


-- created on 2025-11-01
