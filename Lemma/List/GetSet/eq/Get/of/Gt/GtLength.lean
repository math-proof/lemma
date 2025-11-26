import Lemma.List.GetSet.eq.Get.of.Ne.GtLength
import Lemma.Nat.Ne.of.Gt
open List Nat


@[main]
private lemma main
  {x : List α}
-- given
  (h_i : i < x.length)
  (h : d > i)
  (a : α) :
-- imply
  have : i < (x.set d a).length := by simpa
  (x.set d a)[i] = x[i] :=
-- proof
  (GetSet.eq.Get.of.Ne.GtLength h_i ∘ Ne.of.Gt) h _


-- created on 2025-10-05
