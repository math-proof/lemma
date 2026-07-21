import Lemma.Tensor.GetPermute__Neg.as.Permute__Neg_Get.of.GtGet_0.LtAdd_1Length
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthPermute__Neg.eq.Get_0.of.Gt
open Tensor


@[main, cast]
private lemma main
  {s : List ℕ}
  {i k d : ℕ}
-- given
  (h_i : i < s.length)
  (h_k : k < s[0])
  (h_d : i > d)
  (X : Tensor α s) :
-- imply
  (X.permute ⟨i, h_i⟩ (-d)).get ⟨k, by rwa [LengthPermute__Neg.eq.Get_0.of.Gt (by simp; omega)]⟩ ≃ (X.get ⟨k, by rwa [Length.eq.Get_0.of.GtLength_0]⟩).permute ⟨i - 1, by simp; omega⟩ (-d) := by
-- proof
  have := GetPermute__Neg.as.Permute__Neg_Get.of.GtGet_0.LtAdd_1Length (i := i - 1) (d := d) (by grind) h_k (by grind) X
  grind


-- created on 2026-07-04
