import Lemma.List.Set_0.eq.Cons_Tail.of.GtLength_0
open List


@[main]
private lemma main
  [Mul α] [One α]
  {s : List α}
-- given
  (h : s.length > 0)
  (a : α) :
-- imply
  (s.set 0 a).prod = a * s.tail.prod := by
-- proof
  rw [Set_0.eq.Cons_Tail.of.GtLength_0 h]
  simp


-- created on 2025-07-12
