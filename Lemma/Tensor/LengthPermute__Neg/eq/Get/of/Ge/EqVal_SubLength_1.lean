import Lemma.Tensor.Length.of.SEq
import Lemma.Tensor.LengthPermuteTail.eq.Get.of.GtLength_0
import Lemma.Tensor.Permute__Neg.as.PermuteTail.of.Val.eq.SubLength_1
import Lemma.Tensor.SEqPermuteTailS.of.LeLength
open Tensor


@[main]
private lemma main
  {s : List ℕ}
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : i = s.length - 1)
  (h_d : d ≥ i)
  (X : Tensor α s) :
-- imply
  (X.permute i (-d)).length = s[i] := by
-- proof
  have h_pt := Permute__Neg.as.PermuteTail.of.Val.eq.SubLength_1 h X d
  have h_tail := SEqPermuteTailS.of.LeLength (by grind) X (n := d + 1)
  rw [Length.of.SEq h_pt, Length.of.SEq h_tail, LengthPermuteTail.eq.Get.of.GtLength_0 (by grind)]
  grind


-- created on 2026-07-23
