import Lemma.List.Sum.eq.Add_SumDrop
import sympy.vector.vector
open List


@[main]
private lemma main
  [Add α] [Zero α]
  {s : List.Vector α n}
-- given
  (h : n > 0) :
-- imply
  s.sum = s[0] + (s.drop 1).sum := by
-- proof
  have h_len : s.val.length > 0 := by grind
  rw [show s.sum = s.val.sum by rfl]
  rw [Sum.eq.Add_SumDrop (s := s.val) h_len]
  congr


-- created on 2026-07-11
