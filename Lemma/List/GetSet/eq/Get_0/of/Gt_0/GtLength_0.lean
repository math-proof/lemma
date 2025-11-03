import Lemma.List.GetSet.eq.Get.of.Ne.Lt_Length
import Lemma.List.LengthSet.eq.Length
import Lemma.Nat.Ne.of.Gt
open List Nat


@[main]
private lemma main
  {x : List α}
-- given
  (h_x : x.length > 0)
  (h : d > 0)
  (a : α) :
-- imply
  (x.set d a)[0]'(by rwa [LengthSet.eq.Length]) = x[0] := by
-- proof
  apply GetSet.eq.Get.of.Ne.Lt_Length
  apply Ne.of.Gt h


@[main]
private lemma fin
  {x : List α}
-- given
  (h_x : x.length > 0)
  (h : d > 0)
  (a : α) :
-- imply
  (x.set d a).get ⟨0, by rwa [LengthSet.eq.Length]⟩ = x.get ⟨0, by omega⟩ := by
-- proof
  apply main h_x h


-- created on 2025-07-17
