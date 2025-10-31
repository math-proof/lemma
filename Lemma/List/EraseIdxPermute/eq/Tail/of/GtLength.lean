import Lemma.List.EraseIdxPermute.eq.EraseIdx.of.GtLength_Add
open List


@[main]
private lemma main
  {s : List ℕ}
  {d : ℕ}
-- given
  (h : s.length > d) :
-- imply
  (s.permute ⟨0, by grind⟩ d).eraseIdx d = s.tail := by
-- proof
  have := EraseIdxPermute.eq.EraseIdx.of.GtLength_Add (s := s) (i := 0) (d := d) (by omega)
  simp at this
  assumption


-- created on 2025-10-31
