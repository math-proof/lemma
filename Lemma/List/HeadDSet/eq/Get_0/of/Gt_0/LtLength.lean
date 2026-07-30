import Lemma.List.GetSet.eq.Get.of.Ne.GtLength
import Lemma.List.LengthSet.eq.Length
import Lemma.Nat.Ne.of.Gt
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h_s : s.length > 0)
  (h : d > 0)
  (a : α)
  (default : α):
-- imply
  have : (s.set d a).length > 0 := by rwa [LengthSet.eq.Length]
  (s.set d a).headD default = s[0] := by
-- proof
  intro h_length
  rw [HeadD.eq.Get_0.of.GtLength_0 h_length]
  apply GetSet.eq.Get.of.Ne.GtLength
  apply Ne.of.Gt h


-- created on 2025-07-17
