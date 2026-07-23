import Lemma.Tensor.GetPermuteTail.as.Select.of.GtGet.GtLength_0
import Lemma.Tensor.Length.of.SEq
import Lemma.Tensor.LengthPermuteTail.eq.Get.of.GtLength_0
import Lemma.Tensor.LengthPermute__Neg.eq.Get.of.Ge.EqVal_SubLength_1
import Lemma.Tensor.Permute__Neg.as.PermuteTail.of.Val.eq.SubLength_1
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Tensor.SEqPermuteTailS.of.LeLength
open Tensor


@[main, cast]
private lemma main
  {s : List ℕ}
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : i = s.length - 1)
  (h_d : d ≥ i)
  (X : Tensor α s)
  (k : Fin s[i]) :
-- imply
  (X.permute i (-d)).get ⟨k, by rw [LengthPermute__Neg.eq.Get.of.Ge.EqVal_SubLength_1 h h_d]; grind⟩ ≃ X.select ⟨i, by grind⟩ ⟨k, by grind⟩ := by
-- proof
  have h_length := LengthPermute__Neg.eq.Get.of.Ge.EqVal_SubLength_1 h h_d X
  have h_bound : k < (X.permute i (-d)).length := by
    rw [h_length]
    grind
  have h_pt := Permute__Neg.as.PermuteTail.of.Val.eq.SubLength_1 h X d
  have h_tail := SEqPermuteTailS.of.LeLength (by grind) X (n := d + 1)
  apply SEq.trans (SEqGetS.of.SEq.GtLength.fin h_bound h_pt)
  apply SEq.trans (SEqGetS.of.SEq.GtLength.fin (by
    rw [Length.of.SEq h_tail, LengthPermuteTail.eq.Get.of.GtLength_0 (by grind)]
    grind
  ) h_tail)
  have := GetPermuteTail.as.Select.of.GtGet.GtLength_0 (by grind) (by grind) X (k := k)
  grind


-- created on 2026-07-23
