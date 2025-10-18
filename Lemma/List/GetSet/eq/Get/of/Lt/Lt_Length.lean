import Lemma.List.GetSet.eq.Get.of.Ne.Lt_Length
import Lemma.Nat.Ne.of.Lt
open List Nat


@[main]
private lemma main
  {x : List α}
-- given
  (h_i : i < x.length)
  (h : d < i)
  (a : α) :
-- imply
  have : i < (x.set d a).length := by simpa
  (x.set d a)[i] = x[i] :=
-- proof
  (GetSet.eq.Get.of.Ne.Lt_Length h_i ∘ Ne.of.Lt) h _


-- created on 2025-10-05
