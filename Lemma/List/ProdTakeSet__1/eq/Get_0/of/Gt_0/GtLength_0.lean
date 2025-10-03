import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.List.GetSet.eq.Get.of.Ne.Lt_Length
import Lemma.Algebra.Ne.of.Gt
open Algebra List


@[main]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h_s : s.length > 0)
  (h_d : d > 0)
  (a : α) :
-- imply
  ((s.set d a).take 1).prod = s[0] := by
-- proof
  rw [ProdTake_1.eq.Get_0.of.GtLength_0]

  apply GetSet.eq.Get.of.Ne.Lt_Length
  apply Ne.of.Gt h_d


-- created on 2025-07-17
