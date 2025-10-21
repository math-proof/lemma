import Lemma.List.DropPermute.eq.Drop.of.Add.lt.Length
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : d < s.length) :
-- imply
  (s.permute ⟨0, by omega⟩ d).drop (d + 1) = s.drop (d + 1) := by
-- proof
  have := DropPermute.eq.Drop.of.Add.lt.Length (s := s) (i := ⟨0, by omega⟩) (d := d) (by simpa)
  simp at this
  assumption


-- created on 2025-10-21
