import Lemma.List.GetRotate.eq.Get.of.Ge.GtLength.Gt_0
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h_pos : i > 0)
  (h_i : s.length > i) :
-- imply
  (s.rotate (s.length - i))[0]'(by grind) = s[s.length - i] := by
-- proof
  have := GetRotate.eq.Get.of.Ge.GtLength.Gt_0 h_pos h_i (by rfl)
  simp_all


-- created on 2026-04-17
