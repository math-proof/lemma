import Lemma.List.Drop.eq.Nil.of.LeLength
open List


@[main]
private lemma main
  [Mul α] [One α]
  {s : List α}
-- given
  (h : i ≥ s.length) :
-- imply
  (s.drop i).prod = 1 := by
-- proof
  rw [Drop.eq.Nil.of.LeLength h]
  simp


-- created on 2026-07-22
