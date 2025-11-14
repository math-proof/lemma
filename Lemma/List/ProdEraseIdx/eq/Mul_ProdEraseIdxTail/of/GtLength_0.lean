import Lemma.List.EraseIdx.eq.Cons_EraseIdxTail.of.GtLength_0
open List


@[main, comm]
private lemma main
  [Mul α] [One α]
  {s : List α}
-- given
  (h : s.length > 0)
  (i : ℕ) :
-- imply
  (s.eraseIdx i.succ).prod = s[0] * (s.tail.eraseIdx i).prod := by
-- proof
  simp [EraseIdx.eq.Cons_EraseIdxTail.of.GtLength_0 h]


-- created on 2025-11-14
