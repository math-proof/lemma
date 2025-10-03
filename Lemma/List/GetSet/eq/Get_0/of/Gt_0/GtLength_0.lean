import Lemma.List.GetSet.eq.Get.of.Ne.Lt_Length
import Lemma.List.LengthSet.eq.Length
import Lemma.Algebra.Ne.of.Gt
open Algebra List


@[main]
private lemma main
  {x : List α}
-- given
  (h_x : x.length > 0)
  (h : d > 0)
  (a : α) :
-- imply
  have : (x.set d a).length > 0 := by rwa [LengthSet.eq.Length]
  (x.set d a)[0] = x[0] := by
-- proof
  apply GetSet.eq.Get.of.Ne.Lt_Length
  apply Ne.of.Gt h


-- created on 2025-07-17
