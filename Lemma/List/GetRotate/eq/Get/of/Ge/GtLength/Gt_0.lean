import Lemma.List.GetRotate.eq.Ite.of.GeLength.GtLength
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h_pos : j > 0)
  (h_i : s.length > i)
  (h_j : i ≥ j) :
-- imply
  (s.rotate (s.length - i))[i - j]'(by grind) = s[s.length - j] := by
-- proof
  rw [GetRotate.eq.Ite.of.GeLength.GtLength]
  repeat grind


-- created on 2026-04-17
