import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.Tensor.ValDataGetToVector.eq.ValArraySliceData.of.Lt
open Tensor List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h₀ : s.length > 0)
  (h₁ : i < s[0])
  (X : Tensor α s) :
-- imply
  have : i < s.headD 1 := by rwa [← HeadD.eq.Get_0.of.GtLength_0] at h₁
  X.toVector[i].data.val = (X.data.array_slice (i * s.tail.prod) s.tail.prod).val := by
-- proof
  intro h_i
  cases s with
  | nil =>
    contradiction
  | cons h_s t =>
    simp_all
    rw [← ValDataGetToVector.eq.ValArraySliceData.of.Lt]
    rfl


-- created on 2025-06-29
