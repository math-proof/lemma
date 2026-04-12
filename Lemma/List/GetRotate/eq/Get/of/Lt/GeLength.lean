import Lemma.List.GetRotate.eq.Ite.of.GeLength.GtLength
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h_i : s.length ≥ i)
  (h_j : j < i) :
-- imply
  (s.rotate i)[s.length - i + j]'(by grind) = s[j] := by
-- proof
  if h_i : s.length > i then
    rw [GetRotate.eq.Ite.of.GeLength.GtLength]
    repeat grind
  else
    have h_i : s.length = i := by omega
    subst h_i
    simp


-- created on 2026-04-09
-- updated on 2026-04-12
