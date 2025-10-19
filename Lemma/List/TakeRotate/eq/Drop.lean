import Lemma.List.Rotate.eq.AppendDrop__Take
open List


@[main, comm]
private lemma main
-- given
  (s : List α)
  (n : ℕ) :
-- imply
  (s.rotate n).take (s.length - n % s.length) = s.drop (n % s.length) := by
-- proof
  simp [Rotate.eq.AppendDrop__Take]


-- created on 2025-10-19
