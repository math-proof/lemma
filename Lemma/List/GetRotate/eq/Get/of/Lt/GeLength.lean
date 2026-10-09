import Lemma.List.GetRotate.eq.Ite.of.GeLength.GtLength
open List


@[path]
private lemma main
  {s : List α}
-- given
  (h_i : s.length ≥ i)
  (h_j : j < i) :
-- imply
  (s.rotate i)[s.length - i + j]'(by grind [List.length_rotate]) = s[j] := by
-- proof
  if h_i : s.length > i then
    rw [GetRotate.eq.Ite.of.GeLength.GtLength]
    repeat grind [List.length_rotate]
  else
    have h_i : s.length = i := by omega
    subst h_i
    simp


-- created on 2026-04-09
-- updated on 2026-04-12
