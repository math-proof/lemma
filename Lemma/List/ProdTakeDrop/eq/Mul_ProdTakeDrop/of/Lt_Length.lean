import Lemma.List.TakeDrop.eq.Cons_TakeDrop.of.Lt_Length
open List


@[main]
private lemma main
  [Mul α] [One α]
  {s : List α}
-- given
  (h : i < s.length) :
-- imply
  ((s.drop i).take (d + 1)).prod = s[i] * ((s.drop (i + 1)).take d).prod := by
-- proof
  simp [TakeDrop.eq.Cons_TakeDrop.of.Lt_Length h]


-- created on 2025-10-24
