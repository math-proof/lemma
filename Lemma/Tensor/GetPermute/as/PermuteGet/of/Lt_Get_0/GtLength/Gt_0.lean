import Lemma.Tensor.GetPermute.as.PermuteGet.of.Lt_Get_0.LtAdd_1Length
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthPermute.eq.Get_0.of.GtVal_0
open Tensor


@[main, cast]
private lemma main
  {s : List ℕ}
  {i k : ℕ}
-- given
  (h_pos : i > 0)
  (h_i : i < s.length)
  (h_k : k < s[0])
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  (X.permute ⟨i, by omega⟩ d).get ⟨k, by rwa [LengthPermute.eq.Get_0.of.GtVal_0 (by simpa)]⟩ ≃ (X.get ⟨k, by rwa [Length.eq.Get_0.of.GtLength_0]⟩).permute ⟨i - 1, by simp; omega⟩ d := by
-- proof
  have := GetPermute.as.PermuteGet.of.Lt_Get_0.LtAdd_1Length (i := i - 1) (k := k) (by grind) (by grind) X d
  grind


-- created on 2026-07-04
