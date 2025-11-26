import Lemma.List.TakeDrop.eq.Cons_TakeDrop.of.GtLength
open List


@[main]
private lemma main
  [Mul α] [One α]
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  ((s.drop i).take (d + 1)).prod = s[i] * ((s.drop (i + 1)).take d).prod := by
-- proof
  simp [TakeDrop.eq.Cons_TakeDrop.of.GtLength h]


-- created on 2025-10-24
