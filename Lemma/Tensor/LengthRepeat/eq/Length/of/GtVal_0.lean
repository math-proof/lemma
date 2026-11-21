import Lemma.List.GetSet.eq.Get.of.Ne.GtLength
import Def.Data.Tensor.Repeat
import Theorem.Tensor.Length.eq.Get_0.of.GtLength_0
open List Tensor


@[path]
private lemma main
  {d : Fin s.length}
-- given
  (h : d.val > 0)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  (X.repeat d n).length = X.length := by
-- proof
  have h_length : 0 < s.length := Nat.zero_lt_of_lt d.isLt
  have h_set : 0 < (s.set d (n * s[d])).length := by simpa using h_length
  rw [Length.eq.Get_0.of.GtLength_0 h_set, Length.eq.Get_0.of.GtLength_0 h_length]
  apply GetSet.eq.Get.of.Ne.GtLength h_length (Nat.ne_of_gt h)


-- created on 2026-07-04
-- updated on 2026-11-21
