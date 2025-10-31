import Lemma.List.Append_DropTake.eq.Take.of.Ge
open List


@[main, comm]
private lemma main
-- given
  (s : List α)
  (i d : ℕ) :
-- imply
  s.take (i - d) ++ (s.take i).drop (i - d) = s.take i := by
-- proof
  rw [Append_DropTake.eq.Take.of.Ge]
  simp


-- created on 2025-10-31
