import Lemma.List.Permute__Neg.eq.Cons_EraseIdx
import Lemma.List.Permute__Neg.eq.Rotate_SubLength_1.of.GtLength_0
open List


@[main, comm]
private lemma main
  {s : List ℕ}
-- given
  (h : s.length > 0) :
-- imply
  s.rotate (s.length - 1) = s[s.length - 1] :: s.dropLast := by
-- proof
  simp [Rotate_SubLength_1.eq.Permute__Neg.of.GtLength_0 h]
  rw [Permute__Neg.eq.Cons_EraseIdx]
  simp


-- created on 2025-12-03
