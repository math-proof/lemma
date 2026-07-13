import Lemma.Tensor.GetPermute.as.PermuteGet.of.GtGet_0.GtLength.Gt_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthPermute.eq.Get_0.of.Ge_0.GtVal_0
open Tensor


@[main, cast]
private lemma main
  {s : List ℕ}
  {i k : ℕ}
  {d : ℤ}
-- given
  (h_d : d ≥ 0)
  (h_pos : i > 0)
  (h_i : i < s.length)
  (h_k : k < s[0])
  (X : Tensor α s) :
-- imply
  (X.permute ⟨i, by omega⟩ d).get ⟨k, by rwa [LengthPermute.eq.Get_0.of.Ge_0.GtVal_0 (by simpa) (by simpa)]⟩ ≃ (X.get ⟨k, by rwa [Length.eq.Get_0.of.GtLength_0]⟩).permute ⟨i - 1, by simp; omega⟩ d := by
-- proof
  have := GetPermute.as.PermuteGet.of.GtGet_0.GtLength.Gt_0 (i := i) (k := k) (by grind) (by grind) (by grind) X d.toNat
  grind


-- created on 2026-07-04
