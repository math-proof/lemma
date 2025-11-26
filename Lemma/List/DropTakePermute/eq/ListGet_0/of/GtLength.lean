import Lemma.List.DropTakePermute.eq.ListGet.of.GtLength_Add
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length > d) :
-- imply
  ((s.permute ⟨0, by linarith⟩ d).take (d + 1)).drop d = [s[0]] := by
-- proof
  have h := DropTakePermute.eq.ListGet.of.GtLength_Add (s := s) (i := ⟨0, by omega⟩) (d := d) (by grind)
  simp at h
  assumption


-- created on 2025-10-22
-- updated on 2025-10-24
