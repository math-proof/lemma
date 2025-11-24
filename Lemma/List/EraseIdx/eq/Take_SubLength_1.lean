import Lemma.List.DropLast.eq.Take_SubLength_1
open List


@[main]
private lemma main
-- given
  (s : List ℕ) :
-- imply
  s.eraseIdx (s.length - 1) = s.take (s.length - 1) := by
-- proof
  simp [DropLast.eq.Take_SubLength_1]


-- created on 2025-11-24
