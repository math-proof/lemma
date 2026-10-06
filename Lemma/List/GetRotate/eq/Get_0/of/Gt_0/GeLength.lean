import Lemma.List.GetRotate.eq.Get.of.Lt.GeLength
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h_i : s.length ≥ i)
  (h_pos : i > 0) :
-- imply
  (s.rotate i)[s.length - i]'(by grind [List.length_rotate]) = s[0] := by
-- proof
  have := GetRotate.eq.Get.of.Lt.GeLength h_i h_pos
  grind [List.length_rotate]


-- created on 2026-04-11
