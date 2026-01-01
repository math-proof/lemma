import Lemma.List.LengthInsertIdx.eq.Add1Length.of.GeLength
import Lemma.List.GetInsertIdx.eq.Get.of.Gt.GtLength
open List


@[main, fin]
private lemma main
  {s : List α}
-- given
  (h : s.length ≥ i)
  (h_ij : i > j)
  (a : α) :
-- imply
  (s.insertIdx i a)[j]'(by grind) = s[j] := by
-- proof
  apply GetInsertIdx.eq.Get.of.Gt.GtLength _ h_ij


-- created on 2025-10-09
