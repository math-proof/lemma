import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Tensor.GetPermuteTail.as.Select.of.Lt_Get.GtLength_0
import Lemma.Tensor.LengthPermuteTail.eq.Get.of.GtLength_0
open Tensor Bool


@[main]
private lemma main
  {s : List ℕ}
  {k : ℕ}
-- given
  (h_s : s.length > 0)
  (h_k : k < s[s.length - 1])
  (X : Tensor α s) :
-- imply
  (X.permuteTail s.length).get ⟨k, by rwa [LengthPermuteTail.eq.Get.of.GtLength_0 h_s]⟩ = cast (congrArg (Tensor α) (by simp [List.TailRotate.eq.DropLast.of.GtLength_0 h_s])) (X.select ⟨s.length - 1, by grind⟩ ⟨k, by grind⟩) := by
-- proof
  apply Eq_Cast.of.SEq.Eq
  ·
    simp [List.TailRotate.eq.DropLast.of.GtLength_0 h_s]
  ·
    apply GetPermuteTail.as.Select.of.Lt_Get.GtLength_0 h_s h_k


-- created on 2026-04-17
