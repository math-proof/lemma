import Lemma.Algebra.GetSet.eq.Get.of.Ne.Lt_Length
import Lemma.Algebra.LengthSet.eq.Length
import Lemma.Algebra.Ne.of.Gt
import Lemma.Algebra.HeadD.eq.Get_0.of.GtLength_0
open Algebra


@[main]
private lemma main
  {x : List α}
-- given
  (h_x : x.length > 0)
  (h : d > 0)
  (a : α)
  (default : α):
-- imply
  have : (x.set d a).length > 0 := by rwa [LengthSet.eq.Length]
  (x.set d a).headD default = x[0] := by
-- proof
  intro h_length
  rw [HeadD.eq.Get_0.of.GtLength_0 h_length]
  apply GetSet.eq.Get.of.Ne.Lt_Length
  apply Ne.of.Gt h


-- created on 2025-07-17
