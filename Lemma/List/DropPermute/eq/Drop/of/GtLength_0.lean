import Lemma.List.DropPermute.eq.Drop
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length > 0)
  (d : ℕ) :
-- imply
  (s.permute ⟨0, by omega⟩ d).drop (d + 1) = s.drop (d + 1) := by
-- proof
  have := DropPermute.eq.Drop (s := s) (i := ⟨0, by omega⟩) (d := d)
  simp_all


-- created on 2025-10-21
