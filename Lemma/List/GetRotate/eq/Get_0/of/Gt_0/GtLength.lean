import Lemma.List.GetRotate.eq.Get.of.Lt.GtLength
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h_i : s.length > i)
  (h_pos : i > 0) :
-- imply
  (s.rotate i)[s.length - i]'(by grind) = s[0] := by
-- proof
  have := GetRotate.eq.Get.of.Lt.GtLength h_i h_pos
  grind


-- created on 2026-04-11
